-- Prove2me | solution 1 for GlobalTheory.LeviRank.wJac_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:31.941221+00:00
-- url     : https://prove2.me/submissions/05a01c5c-dd54-4910-9001-56b488ce6c29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.LeviRank
namespace GlobalTheory.LeviRank
theorem _root_.solution {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by
  have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
    ext i
    simp [bas, Pi.single_apply]
  conv_rhs => rw [hξ]
  simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hw k), map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end GlobalTheory.LeviRank
