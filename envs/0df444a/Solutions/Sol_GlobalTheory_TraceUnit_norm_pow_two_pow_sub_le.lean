-- Prove2me | solution 1 for GlobalTheory.TraceUnit.norm_pow_two_pow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:59.193244+00:00
-- url     : https://prove2.me/submissions/748eb585-944b-4045-8e7a-a5730b6cc11b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
import Theorems.Thm_GlobalTheory_TraceUnit_norm_sq_sub_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TraceUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.TraceUnit
theorem _root_.solution {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ 2 ^ k - y ^ 2 ^ k‖ ≤ ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2 ^ k) ^ 2 := fun z => by rw [pow_succ, pow_mul]
    rw [e, e]
    exact (norm_sq_sub_sq_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ih
end GlobalTheory.TraceUnit
