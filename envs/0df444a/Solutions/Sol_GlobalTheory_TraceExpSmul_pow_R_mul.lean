-- Prove2me | solution 1 for GlobalTheory.TraceExpSmul.pow_R_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:47.897862+00:00
-- url     : https://prove2.me/submissions/53db6e30-30d9-4655-8fc3-afde0f922ab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero
import Theorems.Thm_GlobalTheory_TraceExpSmul_pow_mul_eq

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
theorem _root_.solution (R N : Matrix n n K) {d : K} (h : N * R = d • (R * N)) (k : ℕ) :
    ∀ m : ℕ, ∃ c : K, (R * N ^ k) ^ m = c • (R ^ m * N ^ (k * m)) := by
  intro m
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * d ^ (k * m), ?_⟩
    rw [pow_succ, hc, smul_mul_assoc, mul_assoc, ← mul_assoc (N ^ (k * m)), pow_mul_eq h,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc, ← pow_succ,
      mul_assoc, ← pow_add, Nat.mul_succ]
end GlobalTheory.TraceExpSmul
