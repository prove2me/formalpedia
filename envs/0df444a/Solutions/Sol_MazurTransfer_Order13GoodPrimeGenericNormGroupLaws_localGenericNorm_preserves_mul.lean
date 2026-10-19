-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.localGenericNorm_preserves_mul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T05:23:02.269721+00:00
-- url     : https://prove2.me/submissions/a82873e6-f735-454a-a57b-266ab7b109d2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: use the complete pinned FLT abelian rigidity proof to
compare the already chosen group laws and prove that the SAME generic
norm morphisms preserve addition over every test scheme.
Named downstream consumer: descent of integral norm multiplication.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormUnit_localGenericNorm_preserves_unit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeLocalPicardModels
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance genericNormMulOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) := actualGroup

namespace MazurTransfer.GoodPrimeGenericNormMulProofHelpers20261018
theorem genericPicard_connected : ConnectedSpace (localGenericPicard q hq).P := by
  letI := (genericPicard_geometry q hq).2.2
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (f := (localGenericPicard q hq).toBase)
end MazurTransfer.GoodPrimeGenericNormMulProofHelpers20261018
open MazurTransfer.GoodPrimeGenericNormMulProofHelpers20261018

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (localGenericPicard q hq).toBase) :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw q hq).mul t x y)
      (localGenericNorm q hq φ) =
    (genericLocalLaw q hq).mul t
      (NeronModelInfra.schemeHomOverComp x (localGenericNorm q hq φ))
      (NeronModelInfra.schemeHomOverComp y (localGenericNorm q hq φ)) := by
  letI := (genericPicard_geometry q hq).1
  letI := (genericPicard_geometry q hq).2.1
  letI := genericPicard_connected q hq
  exact RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    ℚ (f := (localGenericPicard q hq).toBase) (genericLocalLaw q hq) (genericLocalLaw q hq)
    (genericPicard_abelian q hq) (localGenericNorm q hq φ)
    (MazurTransfer.Order13GoodPrimeGenericNormUnit.localGenericNorm_preserves_unit q hq φ) t x y

#print axioms solution
