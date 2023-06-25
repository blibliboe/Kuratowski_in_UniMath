Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.Propositions.

(* Structures used in my proofs have been copied from the original source code *)
Section structure.
  Variable (T A : Type).

  Class hasMembership : Type :=
    member : A -> T -> hProp.

  Class hasSubset : Type :=
    subset : T -> T -> hProp.
  
  Class hasEmpty : Type :=
   empty : T.

  Class hasSingleton : Type :=
    singleton : A -> T.

  Class hasUnion : Type :=
    union : T -> T -> T.
End structure.

Arguments member {_} {_} {_} _ _.
Arguments empty {_} {_}.
Arguments singleton {_} {_} {_} _.
Arguments union {_} {_} _ _.
Arguments subset {_} {_} _ _.


Notation "∅" := empty.
Notation "{| x |}" :=  (singleton x).
Infix "∪" := union (at level 8, right associativity).
Infix "∈" := member (at level 9, right associativity).
Infix  "⊆" := subset (at level 11, right associativity).


Module Export FiniteSet.
  Section FiniteSet.
    Private Inductive FiniteSet (A : Type) : Type :=
      | E: FiniteSet A
      | L: A -> FiniteSet A
      | U: FiniteSet A -> FiniteSet A -> FiniteSet A.

      Global Instance finiteset_empty : forall A, hasEmpty (FiniteSet A) := E.
      Global Instance finiteset_singleton : forall A, hasSingleton (FiniteSet A) A := L.
      Global Instance finiteset_union : forall A, hasUnion (FiniteSet A) := U.

      Variable A : Type.

      Axiom assoc : forall (x y z: FiniteSet A),
        x ∪ (y ∪ z) = (x ∪ y) ∪ z.

      Axiom nl : forall (x : FiniteSet A),
        ∅ ∪ x = x.

      Axiom nr : forall (x : FiniteSet A),
        x ∪ ∅ = x.

      Axiom comm : forall (x y : FiniteSet A),
        x ∪ y = y ∪ x.
      
      Axiom idem : forall (x : A),
        {|x|} ∪ {|x|} = {|x|}.

      Axiom trunc : isaset (FiniteSet A).

  End FiniteSet.

  Arguments assoc {_} _ _ _.
  Arguments comm {_} _ _.
  Arguments nl {_} _.
  Arguments nr {_} _.
  Arguments idem {_} _.



  Section FiniteSet_induction.
    Variable (A : Type)
            (P : FiniteSet A -> Type)
            (H :  forall X : FiniteSet A, isaset (P X))
            (eP : P ∅)
            (lP : forall a: A, P {|a|})
            (uP : forall (x y: FiniteSet A), P x -> P y -> P (x ∪ y))
            (assocP : forall (x y z : FiniteSet A) (px: P x) (py: P y) (pz: P z),
                  transportf P (assoc x y z) (uP x (y ∪ z) px (uP y z py pz))
                  =
                  (uP (x ∪ y) z (uP x y px py) pz))
            (commP : forall (x y: FiniteSet A) (px: P x) (py: P y),
                  transportf P (comm x y) (uP x y px py) = (uP y x py px))
            (nlP : forall (x : FiniteSet A) (px: P x),
                  transportf P (nl x) (uP ∅ x eP px) = px)
            (nrP : forall (x : FiniteSet A) (px: P x),
                  transportf P (nr x) (uP x ∅ px eP) = px)
            (idemP : forall (x : A),
                  transportf P (idem x) (uP {|x|} {|x|} (lP x) (lP x)) = lP x).

    (* Induction principle *)
    Fixpoint FiniteSet_ind
            (x : FiniteSet A)
      : P x
      := (match x return _ -> _ -> _ -> _ -> _ -> _ -> P x with
          | E _ => fun _ _ _ _ _ _ => eP
          | L _ _ => fun _ _ _ _ _ _ => lP _
          | U _ _ _ => fun _ _ _ _ _ _ => uP _ _ (FiniteSet_ind _) (FiniteSet_ind _)
          end) H assocP commP nlP nrP idemP.
  End FiniteSet_induction.


  Section FiniteSet_induction_prop.
    Variable  (A : Type)
              (P : FiniteSet A -> Type)
              (H :  forall X : FiniteSet A, isaprop (P X))
              (eP : P ∅)
              (lP : forall a: A, P {|a|})
              (uP : forall (x y: FiniteSet A), P x -> P y -> P (x ∪ y)).

    (* Recursion principle *)
    Definition FiniteSet_ind_prop (x : FiniteSet A)
    : P x.
    Proof.
      use FiniteSet_ind.
      - intros.
        apply isasetaprop.
        apply H.
      - apply eP.
      - apply lP.
      - apply uP.
      - intros.
        apply H.
      - intros.
        apply H.
      - intros.
        apply H.
      - intros.
        apply H.
      - intros.
        apply H.
    Defined.
  End FiniteSet_induction_prop.

  Section FiniteSet_recursion.
    Variable (A : Type)
             (P : Type)
             (H: isaset P)
             (e : P)
             (l : A -> P)
             (u : P -> P -> P)
             (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
             (commP : forall (x y : P), u x y = u y x)
             (nlP : forall (x : P), u e x = x)
             (nrP : forall (x : P), u x e = x)
             (idemP : forall (x : A), u (l x) (l x) = l x).

    (* Recursion principle *)
    Definition FiniteSet_rec : FiniteSet A -> P.
    Proof.
      use FiniteSet_ind ; try (intros ; rewrite transportf_const) ; cbn.
      - intros.
        apply H.
      - exact e.
      - exact l.
      - intros x y.
        exact u.
      - apply assocP.
      - apply commP.
      - apply nlP.
      - apply nrP.
      - apply idemP.


    Defined.
  End FiniteSet_recursion.

End FiniteSet.


Lemma equality_union (A: Type) : forall (x y: FiniteSet A), (x ∪ x = x) → (y ∪ y = y) → (x ∪ y) ∪ x ∪ y = x ∪ y.
Proof.
  intros x y a b.
  rewrite <- assoc.
  rewrite (comm y (x ∪ y)).
  rewrite <- (assoc x y y).
  rewrite b.
  rewrite assoc.
  rewrite a.
  apply idpath.
Defined.


Definition def_fin_set := FiniteSet.
Definition def_fin_set_ind := FiniteSet_ind.


Definition idempotent_union (A : Type) : forall x: FiniteSet A, x ∪ x = x.
Proof.
  use FiniteSet_ind_prop.
  - intros a.
    simpl.
    apply trunc.
  - simpl.
    apply nl.
  - simpl.
    intro a.
    apply idem.
  - simpl.
    intros x y a b.
    apply equality_union.
    + exact a.
    + exact b.
Defined.


Section Extensionality.

  Global Instance finiteset_member: forall A, hasMembership (FiniteSet A) A.
  Proof.
    intros A a.
    use FiniteSet_rec.
    - apply isasethProp.
    - apply hfalse.
    - apply (fun a' => ischoicebase (a' = a)).
    - intros x y.
      apply (hdisj x y).
    - intros x y z.
      simpl.
      apply pathsinv0.
      apply isassoc_hdisj.
    - simpl.
      intros.
      rewrite iscomm_hdisj.
      reflexivity.
    - simpl.
      intros.
      apply hfalse_hdisj.
    - intros.
      simpl.
      apply hPropUnivalence.
      {apply hinhuniv.
        intros.
        induction X as [hG|hP].
        + exact hG.
        + induction hP.
      } intros.
      apply (hinhpr (ii1 X)).
    - intros.
      simpl.
      apply hPropUnivalence.
      {apply hinhuniv.
        intros.
        induction X as [hG|hP].
        + exact hG.
        + exact hP.
      } intros.
      apply (hinhpr (ii2 X)).
    Defined.


    Global Instance finiteset_subset: forall A, hasSubset (FiniteSet A).
    Proof.
      intros A Y.
      use FiniteSet_rec.
      - apply isasethProp.
      - apply htrue.
      - apply (fun a => a ∈ Y).
      - intros x y.
        apply (hconj x y).
      - intros.
        simpl.
        rewrite isassoc_hconj.
        reflexivity.
      - intros. simpl.
        rewrite iscomm_hconj.
        reflexivity.
      - simpl.
        intros.
        apply htrue_hconj.
      - simpl.
        intros.
        rewrite iscomm_hconj.
        apply htrue_hconj.
      - intros.
        simpl.
        apply hPropUnivalence.
        {intros. 
          apply (pr1 X).
        }intros.
        split.
        + exact X.
        + exact X.
      Defined.
End Extensionality.

Section ext.
  Context {A : Type}.

  Lemma equiv_subset1_l (X Y : FiniteSet A) (H1 : Y ∪ X = X) (a : A) (Ya : a ∈ Y) : a ∈ X.
  Proof.
    apply (transportf (fun Z => a ∈ Z) H1 (hinhpr(ii1 Ya))).
  Defined.

  Lemma equiv_subset X: forall (Y : FiniteSet A), (forall (a: A), a ∈ Y → a ∈ X) → Y ∪ X = X.
  Proof.
    use FiniteSet_ind_prop.
    - intros.
      simpl.
      admit.
    - simpl.
      intros.
      apply nl.
    - intro b.
      intro sub.
      specialize (sub b).
      revert sub.
      revert X.
      use FiniteSet_ind_prop.
      + intros.
        admit.
      + simpl.
        intros.
        admit.
      + intros.
        simpl.
        intros.
        admit.
      + intros.
        simpl.
        intros.
        admit.
    - intros Y1 Y2 H1 H2 H3.
      rewrite <- assoc.
      rewrite (H2 (fun a HY => H3 a (hinhpr(inr HY)))).
      apply (H1 (fun a HY => H3 a (hinhpr(inl HY)))).
  Admitted.  



  Lemma eq_subset2 (X Y : FiniteSet A) : X = Y ≃ (Y ∪ X = X) × (X ∪ Y = Y).
  Proof.
    admit.
  Admitted.
  
  Theorem fset_ext (X Y : FiniteSet A) :
    X = Y ≃ forall (a : A), a ∈ X = a ∈ Y.
  Proof.
    admit.
  Admitted.

  Lemma subset_union (X Y : FiniteSet A) :
    X ⊆ Y -> X ∪ Y = Y.
  Proof.
    revert X.
    use FiniteSet_ind_prop.
    - intros.
      admit.
    - simpl.
      intros.
      apply nl.
    - intros a.
      revert Y.
      use FiniteSet_ind_prop.
      + intros.
        admit.
      + intro.
        admit.
      + intros b p.
        admit.
      + intros X1 X2 IH1 IH2 t.
        admit.
    - intros X1 X2 IH1 IH2 G.
      rewrite <- assoc.
      admit.
  Admitted.
        

  Lemma subset_union_l (X : FiniteSet A) :
    forall Y, X ⊆ X ∪ Y.
  Proof.
    revert X.
    use FiniteSet_ind_prop.
    - intros.
      admit.
    - simpl.
      intros.
      admit.
    - intros.
      simpl.
      admit.      
    - intros X1 X2 HX1 HX2 Y.
      split ; unfold subset in *.
      + admit.
      + admit.
  Admitted.

  Search ((_ -> _ ) -> (_ -> _) -> (_ ≃ _)).

  Lemma subset_union_equiv
    : forall X Y : FiniteSet A, X ⊆ Y ≃ X ∪ Y = Y.
  Proof.
    intros X Y.
    admit.
  Admitted.
  
  Lemma subset_isIn (X Y : FiniteSet A) :
    X ⊆ Y ≃ forall (a : A), a ∈ X -> a ∈ Y.
  Proof.
    admit.
  Admitted.

  Lemma eq_subset (X Y : FiniteSet A) :
    X = Y ≃ (Y ⊆ X × X ⊆ Y).
  Proof.
    admit.
  Admitted.


End ext.

