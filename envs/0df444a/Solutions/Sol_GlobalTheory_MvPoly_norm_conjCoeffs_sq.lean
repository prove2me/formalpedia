-- Prove2me | solution 1 for GlobalTheory.MvPoly.norm_conjCoeffs_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:39.836718+00:00
-- url     : https://prove2.me/submissions/ba11b02c-cb16-4dfa-8377-78501e559896

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_MvPoly_support_subset_monomialsLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
variable [NumberField K] [Fintype σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution [DecidableEq σ] {D : ℕ} {P : MvPolynomial σ K}
    (hP : P.totalDegree ≤ D) :
    ‖conjCoeffs K σ D P‖ ^ 2 = ∑ s : K →+* ℂ, l2Norm (map s P) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [l2Norm_eq_sqrt_sum_of_subset
    ((support_map_subset s P).trans (support_subset_monomialsLE.2 hP)),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← Finset.sum_coe_sort (monomialsLE σ D)]
  simp only [conjCoeffs, coeff_map, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
end GlobalTheory.MvPoly
