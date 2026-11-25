-- Prove2me | solution 1 for GlobalTheory.LeadJets.leadVal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:18.142927+00:00
-- url     : https://prove2.me/submissions/a317c7e2-84f5-471d-b9c7-8eb37756c282

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
import Theorems.Thm_GlobalTheory_LeadJets_mem_multiLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
namespace GlobalTheory.LeadJets
theorem _root_.solution {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) {T a0 a : ℕ}
    (ha : a < a0) (ha0 : a0 ≤ T + 1) (cc dd : (Fin n → ℕ) → Fin δ → ℂ) (hw : w ≠ 0) :
    leadVal s w t T a0 (fun α k => cc α k + if ∑ q, α q = a then dd α k else 0) =
      leadVal s w t T a0 cc + ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
        (w ^ T * ∑ k, dd α k * t k) * ∏ k, (s k / w) ^ α k := by
  classical
  have hfil : (multiLt n a0).filter (fun α => ∑ q, α q = a) =
      Finset.Nat.antidiagonalTuple n a := by
    ext α
    simp only [Finset.mem_filter, mem_multiLt, Finset.Nat.mem_antidiagonalTuple]
    omega
  unfold leadVal
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlt := mem_multiLt.1 hα
  by_cases h : ∑ q, α q = a
  · simp only [if_pos h]
    have hm : (∏ q, s q ^ α q) = (∏ k, (s k / w) ^ α k) * w ^ (∑ q, α q) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_pow, div_mul_cancel₀ _ hw]
    have hT : w ^ (∑ q, α q) * w ^ (T - ∑ q, α q) = w ^ T := by
      rw [← pow_add]; congr 1; omega
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hm]
    linear_combination (dd α k * (∏ q, (s q / w) ^ α q) * t k) * hT
  · simp [h]
end GlobalTheory.LeadJets
