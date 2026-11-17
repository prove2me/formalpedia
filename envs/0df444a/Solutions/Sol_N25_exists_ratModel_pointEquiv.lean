-- Prove2me | solution 1 for N25.exists_ratModel_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:08.81505+00:00
-- url     : https://prove2.me/submissions/cf48db5b-272a-4048-9572-a82fd6c952c8

import Mathlib
import Definitions.Def_N25
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace N25

/-- A geometric morphism fixed by every arithmetic automorphism descends to the rational field. -/
private theorem rational_point_descent {X : Scheme.{0}}
    (x : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X)
    (hx : ∀ σ : Gal, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of ℚ) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ y = x := by
  let : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    { isAlgClosed := AlgebraicClosure.isAlgClosed ℚ
      isAlgebraic := ⟨fun z => by
        have hz : IsIntegral ℚ z := by
          convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
          all_goals rfl
        exact hz.isAlgebraic⟩ }
  let : IsGalois ℚ (AlgebraicClosure ℚ) :=
    { to_isSeparable := IsAlgClosure.separable ℚ (AlgebraicClosure ℚ)
      to_normal := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) }
  have hd := Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    (⊤ : Subgroup Gal) x (fun σ _ => hx σ)
  rw [InfiniteGalois.fixedField_bot] at hd
  obtain ⟨y, hy⟩ := hd
  let e := IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  convert hy using 2
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact congrArg Subtype.val (e.symm_apply_apply a)

/-- Arithmetic fixed points of the modular Jacobian are the rational points of its model,
with the group law induced from that model. -/
private theorem rational_pointEquiv_of_model
    (hmodel : ∃ (B : Scheme.{0})
      (f : B ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt 2)))
      (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt 2) f)
      (pts : J ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ)))) f),
      AbelianSchemePropertyBundle ℚ (RelativeGroupLaw.genericFibreStr ℚ f) ∧
      L.IsCommutative ∧
      (∀ x y : J, pts (x + y) = L.mul _ (pts x) (pts y)) ∧
      (∀ (σ : Gal) (x : J), (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pts x).1)) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of ℚ)) (G : RelativeGroupLaw ℚ f)
      (e : ↥N25.M ≃ Scheme.KPoint f),
      G.IsCommutative ∧ AbelianSchemePropertyBundle ℚ f ∧
      ∀ x y : ↥N25.M, e (x + y) = G.mul (𝟙 _) (e x) (e y) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨B, f, L, pts, hB, hcomm, hadd, hgal⟩ := hmodel
  let s := specGenericFibreInclusion ↥(GaloisRep.ratLocalizedAt 2) ℚ
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  let k := Spec.map (CommRingCat.ofHom
    (algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ)))
  have hbs : b ≫ s = k := by
    dsimp [b, s, k, specGenericFibreInclusion]
    rw [← Spec.map_comp]
    congr 1
  let : Epi b := Flat.epi_of_flat_of_surjective b
  let extend : SchemeHomOver s f → J := fun q =>
    pts.symm (GoodReductionJacobian.schemeHomOverComp b hbs q)
  have hextend (q : SchemeHomOver s f) : pts (extend q) =
      GoodReductionJacobian.schemeHomOverComp b hbs q := pts.apply_symm_apply _
  have hfixed (q : SchemeHomOver s f) : extend q ∈ M := by
    intro σ
    apply pts.injective
    apply Subtype.ext
    rw [hgal, hextend]
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (b ≫ q.1) = b ≫ q.1
    rw [← Category.assoc]
    congr 1
    dsimp [b]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact σ.commutes a
  let liftPoint : SchemeHomOver s f → ↥M := fun q => ⟨extend q, hfixed q⟩
  have hlift_inj : Function.Injective liftPoint := by
    intro q r h
    apply Subtype.ext
    apply (cancel_epi b).mp
    have hp := congrArg (fun z : ↥M => (pts z.1).1) h
    simpa only [liftPoint, hextend, GoodReductionJacobian.schemeHomOverComp_coe] using hp
  have hlift_surj : Function.Surjective liftPoint := by
    intro x
    obtain ⟨y, hy⟩ := rational_point_descent (pts x.1).1 (fun σ => by
      exact (hgal σ x.1).symm.trans (congrArg (fun z => (pts z).1) (x.2 σ)))
    have hyover : y ≫ f = s := by
      apply (cancel_epi b).mp
      rw [← Category.assoc, hy]
      exact (pts x.1).2.trans hbs.symm
    refine ⟨⟨y, hyover⟩, ?_⟩
    apply Subtype.ext
    apply pts.injective
    apply Subtype.ext
    change (pts (extend ⟨y, hyover⟩)).1 = (pts x.1).1
    rw [hextend]
    exact hy
  let E : SchemeHomOver s f ≃ ↥M := Equiv.ofBijective liftPoint ⟨hlift_inj, hlift_surj⟩
  have hEadd (q r : SchemeHomOver s f) : E (L.mul s q r) = E q + E r := by
    apply Subtype.ext
    apply pts.injective
    change pts (extend (L.mul s q r)) = pts (extend q + extend r)
    rw [hextend, hadd, hextend, hextend]
    exact L.mul_natural s k b hbs q r
  let A := RelativeGroupLaw.genericFibreScheme ℚ f
  let fQ := RelativeGroupLaw.genericFibreStr ℚ f
  let G := L.genericFibre ℚ
  let F : Scheme.KPoint fQ ≃ SchemeHomOver s f :=
    (RelativeGroupLaw.baseChangePointEquiv s (𝟙 _)).trans
      (Equiv.cast (by rw [Category.id_comp]))
  let e := E.symm.trans F.symm
  refine ⟨A, fQ, G, e, RelativeGroupLaw.IsCommutative.baseChange s hcomm,
    hB, ?_⟩
  intro x y
  apply F.injective
  have hF (z : ↥M) : F (e z) = E.symm z := F.apply_symm_apply _
  rw [hF]
  have hmul : F (G.mul (𝟙 _) (e x) (e y)) = L.mul s (F (e x)) (F (e y)) := by
    exact RelativeGroupLaw.baseChangePointToBase_mul s L (𝟙 _) (e x) (e y)
  rw [hmul, hF, hF]
  apply E.injective
  simp only [hEadd, E.apply_symm_apply]

/-- Arithmetic fixed points are rational points for the law on the model's generic fibre. -/
theorem _root_.solution :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of ℚ)) (G : RelativeGroupLaw ℚ f)
      (e : ↥N25.M ≃ Scheme.KPoint f),
      G.IsCommutative ∧ AbelianSchemePropertyBundle ℚ f ∧
      ∀ x y : ↥N25.M, e (x + y) = G.mul (𝟙 _) (e x) (e y) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨B, f, L, pts, hB, hcomm, hadd, hgal, _⟩ :=
    ModularCurve.exists_abelianSchemePropertyBundle_model_jH 25 H25 2 (by decide)
  exact rational_pointEquiv_of_model ⟨B, f, L, pts,
    hB.of_isPullback (IsPullback.of_hasPullback f
      (specGenericFibreInclusion ↥(GaloisRep.ratLocalizedAt 2) ℚ)),
    hcomm, hadd, fun σ x => hgal σ x⟩

end N25
