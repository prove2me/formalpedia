-- Prove2me | solution 1 for GlobalTheory.TraceExpSmul.trace_R_mul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:03:02.136531+00:00
-- url     : https://prove2.me/submissions/bed501b6-7d3c-45f0-ae98-800554667ec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero
import Theorems.Thm_GlobalTheory_TraceExpSmul_pow_R_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceExpSmul
open Finset
variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]
namespace GlobalTheory.TraceExpSmul
theorem _root_.solution {R N : Matrix n n K} (hN : IsNilpotent N) {d : K}
    (h : N * R = d • (R * N)) (k : ℕ) (hk : 1 ≤ k) : Matrix.trace (R * N ^ k) = 0 := by
  obtain ⟨p, hp⟩ := hN
  have hnil : IsNilpotent (R * N ^ k) := by
    obtain ⟨c, hc⟩ := pow_R_mul R N h k p
    refine ⟨p, ?_⟩
    rw [hc, pow_eq_zero_of_le (Nat.le_mul_of_pos_left p hk) hp, mul_zero, smul_zero]
  exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
end GlobalTheory.TraceExpSmul
