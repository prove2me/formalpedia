-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeGenericNormUnit.localGenericNorm_preserves_unit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:55:10.457421+00:00
-- url     : https://prove2.me/submissions/e18310a0-0746-4b06-accb-4862e6dc77dc

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the already transported actual norm morphisms preserve
zero for the generic fibre of the SAME local integral group law.
Named downstream consumer: field rigidity and integral norm group laws.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm
open Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance genericNormUnitOriginalGroupProvider120261018 : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance genericNormUnitOriginalGroupProvider220261018 : GrpObj (Over.mk (localGenericPicard q hq).toBase) :=
  (genericRepresentationGroup q hq).grpObj

namespace MazurTransfer.GoodPrimeGenericNormUnitProofHelpers20261018
theorem localGenericNorm_isMonHom
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    IsMonHom ((actualLocalGenericOverIso q hq).inv ≫ φ ≫
      (actualLocalGenericOverIso q hq).hom) := by
  letI := actualLocalGenericOverIso_isMonHom q hq
  infer_instance

end MazurTransfer.GoodPrimeGenericNormUnitProofHelpers20261018
open MazurTransfer.GoodPrimeGenericNormUnitProofHelpers20261018

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw q hq).one (𝟙 _))
      (localGenericNorm q hq φ) = (genericLocalLaw q hq).one (𝟙 _) := by
  letI := localGenericNorm_isMonHom q hq φ
  have h := congrArg (fun f : Over.mk (𝟙 (Spec (CommRingCat.of ℚ))) ⟶
    Over.mk (localGenericPicard q hq).toBase => f.left)
    (MonObj.one_comp ((actualLocalGenericOverIso q hq).inv ≫ φ ≫
      (actualLocalGenericOverIso q hq).hom))
  change ((genericRepresentedLaw q hq).one (𝟙 _)).val ≫
    (localGenericNorm q hq φ).val = ((genericRepresentedLaw q hq).one (𝟙 _)).val at h
  apply Subtype.ext
  change ((genericLocalLaw q hq).one (𝟙 _)).val ≫
    (localGenericNorm q hq φ).val = ((genericLocalLaw q hq).one (𝟙 _)).val
  rw [generic_group_law_units_equal]
  exact h

#print axioms solution
