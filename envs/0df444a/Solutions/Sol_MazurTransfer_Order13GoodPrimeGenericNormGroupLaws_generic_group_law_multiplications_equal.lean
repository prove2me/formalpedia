-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.generic_group_law_multiplications_equal
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:50:04.116131+00:00
-- url     : https://prove2.me/submissions/b527db0c-82a5-4926-a172-6735f3990da8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: use the complete pinned FLT abelian rigidity proof to
compare the already chosen group laws and prove that the SAME generic
norm morphisms preserve addition over every test scheme.
Named downstream consumer: descent of integral norm multiplication.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeLocalPicardModels
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
namespace MazurTransfer.GoodPrimeGenericPicardConnectedProofHelpers20261018
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
theorem genericPicard_connected : ConnectedSpace (localGenericPicard q hq).P := by
  letI := (genericPicard_geometry q hq).2.2
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (f := (localGenericPicard q hq).toBase)
end MazurTransfer.GoodPrimeGenericPicardConnectedProofHelpers20261018
open MazurTransfer.GoodPrimeGenericPicardConnectedProofHelpers20261018

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (localGenericPicard q hq).toBase) :
    (genericLocalLaw q hq).mul t x y = (genericRepresentedLaw q hq).mul t x y := by
  letI := (genericPicard_geometry q hq).1
  letI := (genericPicard_geometry q hq).2.1
  letI := genericPicard_connected q hq
  have h := RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    ℚ (f := (localGenericPicard q hq).toBase) (genericLocalLaw q hq) (genericRepresentedLaw q hq)
    (genericPicard_abelian q hq) (schemeHomOverId (localGenericPicard q hq).toBase)
    (by
      apply Subtype.ext
      change ((genericLocalLaw q hq).one (𝟙 _)).val ≫ 𝟙 _ =
        ((genericRepresentedLaw q hq).one (𝟙 _)).val
      rw [Category.comp_id]
      exact congrArg Subtype.val (generic_group_law_units_equal q hq)) t x y
  erw [NeronModelInfra.schemeHomOverComp_id_right,
    NeronModelInfra.schemeHomOverComp_id_right,
    NeronModelInfra.schemeHomOverComp_id_right] at h
  exact h

#print axioms solution
