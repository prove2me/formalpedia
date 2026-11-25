-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_norm_coeff_detProdPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:29.276687+00:00
-- url     : https://prove2.me/submissions/45bf9739-e463-4398-8610-e6cf9c1d109a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_norm_coeff_detProdPoly_le
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_eval_detProdPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.DiscEval
theorem _root_.solution {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : ∃ μ, ‖coeff μ (detProdPoly K n)‖ = 1 := by
  by_contra! h
  have h1 : eval (entries fun s => (1 : Matrix (n s) (n s) K)) (detProdPoly K n) = 1 := by
    simp [eval_detProdPoly]
  have h2 : ‖eval (entries fun s => (1 : Matrix (n s) (n s) K)) (detProdPoly K n)‖ < 1 := by
    rw [eval_eq]
    refine norm_lt_of_hasSum one_pos (Finset.hasSum _ _) fun μ => ?_
    rw [Function.comp_apply, norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt
      ((norm_coeff_detProdPoly_le n _).lt_of_ne (h _))
    rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    simp only [entries, Matrix.one_apply]
    split_ifs <;> simp
  simp [h1] at h2
end GlobalTheory.DiscEval
