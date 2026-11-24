-- Prove2me | solution 1 for GlobalTheory.TraceUnit.norm_sub_lt_one_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:57.607074+00:00
-- url     : https://prove2.me/submissions/ae3490ee-98a7-40cb-8cd3-4122b12d8c01

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
import Theorems.Thm_GlobalTheory_TraceUnit_norm_sub_le_max_of_ultra

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
theorem _root_.solution {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : ‖x ^ 2 - y ^ 2‖ < 1) : ‖x - y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hle : ‖x - y‖ ≤ 1 := (norm_sub_le_max_of_ultra x y).trans (max_le hx hy)
  have heq : ‖x - y‖ = 1 := le_antisymm hle hc
  have e : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * y * (x - y) := by ring
  have hA : ‖(x - y) ^ 2‖ = 1 := by rw [norm_pow, heq, one_pow]
  have hB : ‖2 * y * (x - y)‖ < 1 := by
    rw [norm_mul, norm_mul, heq, mul_one]
    calc ‖(2 : K)‖ * ‖y‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h2
  have h3 : ‖(x - y) ^ 2 + 2 * y * (x - y)‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hA]; exact hB.ne'), hA]
    exact max_eq_left hB.le
  rw [e, h3] at h
  exact lt_irrefl _ h
end GlobalTheory.TraceUnit
