-- Prove2me | solution 1 for GlobalTheory.TraceUnit.norm_sub_lt_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:00.865731+00:00
-- url     : https://prove2.me/submissions/1791c491-395e-4e75-bc4c-21cc1f1b9478

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
import Theorems.Thm_GlobalTheory_TraceUnit_norm_sub_lt_one_of_sq

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
theorem _root_.solution {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ)
    (h : ‖x ^ 2 ^ k - y ^ 2 ^ k‖ < 1) : ‖x - y‖ < 1 := by
  induction k generalizing x y with
  | zero => simpa using h
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2) ^ 2 ^ k := fun z => by rw [pow_succ', pow_mul]
    rw [e, e] at h
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hy2 : ‖y ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    exact norm_sub_lt_one_of_sq h2 hx hy (ih hx2 hy2 h)
end GlobalTheory.TraceUnit
