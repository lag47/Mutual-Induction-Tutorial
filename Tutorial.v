Require Export Coq.omega.Omega.
Section FiniteSet.

  Class FiniteSet (A : Type) :=
    {
      t : Type;
      contains : A -> t -> bool;
      add : A -> t -> t;
      union : t -> t -> t;
      cardinal : t -> nat;
      empty : t;
      add_idemp : forall a b s, contains a s = true -> contains a (add b s) = true;
      add_contains : forall a s, contains a (add a s) = true;
      cardinal_bound : forall s s', cardinal (union s s') <= cardinal s + cardinal s';
      empty_contains : forall a, contains a empty = false;
      add_cardinal_bound : forall a s, cardinal (add a s) <= 1 + cardinal s;
      cardinal_empty : cardinal empty = 0;
      cardinal_not_in : forall a s, contains a s = false -> cardinal (add a s) = 1 + cardinal s;
      union_empty : forall s, union s empty = s;
    }.
  Definition single {A } {FS : FiniteSet A} (a : A) := add a empty.
  Notation "s1 ∪ s2" := (union s1 s2) (at level 60).


  Lemma singleton_size : forall A (FS : FiniteSet A) a, cardinal (single a) = 1.
    Proof.
      intros. unfold single. specialize (cardinal_not_in a empty) as H.
      specialize (H (empty_contains a)). rewrite cardinal_empty in H. auto.
    Qed.

End FiniteSet.

Section PDL.
  Context (prog prop : Type).
  
  Notation "s1 ∪ s2" := (union s1 s2) (at level 60).
  Inductive pdl_formula := 
    | AtomF (p : prop)
    | Box (α : pdl_program) (φ : pdl_formula)
    | Imp (φ ψ : pdl_formula)
    | Bot
  with pdl_program :=
    | AtomP (p : prog)
    | Plus (α β : pdl_program)
    | Seq (α β : pdl_program)
    | Star (α : pdl_program)
    | TestP (φ : pdl_formula)
  .
  Context (FS : FiniteSet pdl_formula).

  Fixpoint formula_length (φ : pdl_formula) :=
    match φ with
    | AtomF _ => 1
    | Box α φ => 1 + program_length α + formula_length φ
    | Imp φ ψ => 1 + formula_length φ + formula_length ψ
    | Bot => 1
  end
  with program_length (α : pdl_program) :=
    match α with
    | AtomP _ => 1
    | Plus α β => 1 + program_length α + program_length β
    | Seq α β => 1 + program_length α + program_length β
    | Star α => 1 + program_length α
    | TestP φ => 1 + formula_length φ
  end.

  Definition max x y := if x <? y then y else x.

  Lemma max_le_plus : forall x y, max x y <= x + y.
  Proof.
    intros. unfold max. destruct (x <? y); omega.
  Qed.

  Fixpoint formula_height φ :=
    match φ with
    | AtomF _ | Bot => 1
    | Imp ϕ ψ => 1 + max (formula_height ϕ) (formula_height ψ)
    | Box α ψ => 1 + max (formula_height ψ) (program_height α) end
   with program_height α :=
    match α with
    | AtomP _ => 1 
    | Plus α β => 1 + max (program_height α) (program_height β)
    | Seq α β  =>  1 + max (program_height α) (program_height β)
    | Star α => 1 + program_height α
    | TestP φ => 1 + formula_height φ end.

  Ltac solve_hs :=
    simpl;
    do 30 match goal with
    | |- context [ max ?x ?y  ] => unfold max
    | |- context [ ?x <? ?y  ] => destruct (x <? y)
    | _ => try omega end.


  Lemma height_le_size_pdl : forall φ, formula_height φ <= formula_length φ.
    Proof.
      induction φ; intros; solve_hs.
      enough (forall α, program_height α <= program_length α).
      - specialize (H α). solve_hs.
      - induction α0; solve_hs.
        (* this is basically our original goal... inducting won't give new information  *)
    Abort.

  Scheme pdl_formula_program := Induction for pdl_formula Sort Prop 
                                                    with pdl_program_formula := Induction for pdl_program Sort Prop.
  Combined Scheme pdl_formula_program_mutind from pdl_formula_program, pdl_program_formula.


  (*So for one of the cases of formula, we needed a proposition on programs, and for one of the cases of
    program we needed one for formula. Cases like these often get solved with mutual induction*)

  Lemma height_le_size_pdl' : (forall φ, formula_height φ <= formula_length φ) /\
                             (forall α, program_height α <= program_length α).
    Proof.
      apply pdl_formula_program_mutind; intros; solve_hs.
    Qed.

  Lemma height_le_size_pdl : forall φ, formula_height φ <= formula_length φ.
  Proof.
    destruct height_le_size_pdl'. auto.
  Qed.


  Fixpoint fl_closure φ  : t :=
    match φ with
    | AtomF _ | Bot => single φ
    | Imp ϕ ψ => (single φ) ∪ (fl_closure ϕ) ∪ (fl_closure ψ)
    | Box α ψ => (fl_closure_box α ψ) ∪ fl_closure ψ
    end
  with fl_closure_box α φ:=
    single (Box α φ) ∪
    match α with
    | AtomP p => empty
    | Plus α β => fl_closure_box α φ ∪ fl_closure_box β φ
    | Seq α β => fl_closure_box α (Box β φ) ∪ fl_closure_box β φ
    | Star α => fl_closure_box α (Box (Star α) φ)
    | TestP ψ => fl_closure ψ
   end.

(*tactic that accomplishes basic finite set size reasoning for the following proofs*)

Ltac union_len :=
  simpl;
  do 30 match goal with
  | |- context [union ?s empty] => rewrite union_empty
  | |- context [ (single ?x)  ] =>
    specialize (singleton_size _ _ x); intros; remember (single x); try omega
  | |- cardinal (?s1 ∪ ?s2) <= _ => rewrite (cardinal_bound s1 s2)
  | |- context [union ?s1 ?s2] => specialize (cardinal_bound s1 s2); intros;
                                  remember (union s1 s2); try omega
  | _ => omega
end.

  (* write a tactic to do most reasoning  *)
  Lemma size_bound : forall φ, cardinal (fl_closure φ) <= formula_length φ.
    induction φ; try union_len. 
    simpl. 
    (*Now we need some condition bounding fl_closure_box α φ...*)
    enough (H : forall φ, cardinal (fl_closure_box α φ) <= program_length α); try ( specialize (H φ); union_len).
    (*  *)
    induction α; intros.
    - union_len.
    - specialize (IHα1 φ0); specialize (IHα2 φ0); union_len.
    - simpl. specialize (IHα1 (Box α2 φ0)). specialize (IHα2 φ0). union_len.
    - simpl. specialize (IHα (Box (Star α) φ0)). union_len.
    - simpl. rewrite cardinal_bound. rewrite singleton_size. simpl.
      (* This is our original  goal...*)
    Abort.


  Lemma size_bound' : (forall φ, cardinal (fl_closure φ) <= formula_length φ) /\
                      (forall α φ, cardinal (fl_closure_box α φ) <= program_length α).
    Proof.
      apply pdl_formula_program_mutind; intros; try union_len.
      (*Previously problematic box case*)
      - specialize (H φ). union_len.
      - specialize (H φ); specialize (H0 φ); union_len.
      - specialize (H (Box β φ)). specialize (H0 φ). union_len.
      - specialize (H (Box (Star α) φ)). union_len.
    Qed.

  Lemma size_bound : forall φ, cardinal (fl_closure φ) <= formula_length φ.
    Proof.
      destruct size_bound'. auto.
    Qed.

End PDL.

Section HiddenMutualInduction.
  Context (A : Type).
          
  Inductive Sexpr :=
    | SexprList (l : list Sexpr)
    | Atom (a : A) .

  Fixpoint sum l := 
    match l with
    | nil => 0
    | (h :: t)%list => h + sum t end.

  Fixpoint maxl l :=
    match l with
    | nil => 0
    | (h :: t)%list => 
      let m := maxl t in
      if (m <? h) then h else m end.

  Lemma max_lt_sum : forall l, maxl l <= sum l.
  Proof.
    induction l; auto. simpl. destruct (maxl l <? a); try omega.
  Qed.

  Fixpoint size (s : Sexpr) :=
    match s with
    | Atom _ => 1
    | SexprList l => 1 + sum (List.map size l) end.

  Fixpoint height (s : Sexpr) :=
    match s with
    | Atom _ => 1
    | SexprList l => 1 + maxl (List.map height l) end.


  Lemma height_le_size : forall s, height s <= size s.
    Proof.
      induction s; auto.
      induction l; auto. simpl. Fail omega.
      (*no information about the height or size of the elements of l*)
    Abort.
    (*based on Chlipala sort of*)
  Section sexpr_ind'.
    Variable (P : Sexpr -> Prop).

    Hypothesis (AtomCase : forall a, P (Atom a)).

    Hypothesis (ListCase : forall l, List.Forall P l -> P (SexprList l)).

    Fail Fixpoint sexpr_ind' (s : Sexpr) : P s :=
      match s with
      | Atom a => AtomCase a
      | SexprList l => ListCase l (list_sexpr_ind l) end
     with list_sexpr_ind (l : list Sexpr) : List.Forall P l :=
      match l with
      | nil => @List.Forall_nil Sexpr P
      | (h :: t)%list => @List.Forall_cons Sexpr P h t (sexpr_ind' h) (list_sexpr_ind t) end.

    Fixpoint sexpr_ind' (s : Sexpr) : P s :=
      match s with
      | Atom a => AtomCase a
      | SexprList l => ListCase l (
              (fix list_sexpr_ind (l : list Sexpr) :=
                   match l with
                   | nil => @List.Forall_nil Sexpr P
                   | (h :: t)%list => @List.Forall_cons Sexpr P h t (sexpr_ind' h) (list_sexpr_ind t) end
                                  ) l) end.
   End sexpr_ind'.

   Lemma height_le_size : forall s, height s <= size s.
   Proof.
     apply sexpr_ind'; auto.
     intros. induction l; auto. inversion H. subst.
     simpl. destruct (maxl (List.map height l) <? height a); try omega.
     specialize (IHl H3). simpl in IHl. omega.
   Qed.
 
End HiddenMutualInduction.
