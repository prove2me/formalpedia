-- Prove2me | solution 1 for GlobalTheory.TraceExpSmul.pow_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:07.394397+00:00
-- url     : https://prove2.me/submissions/272a04e8-a584-4d81-ba40-63bd56c4c8ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero

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
theorem _root_.solution {R N : Matrix n n K} {d : K} (h : N * R = d • (R * N)) :
    ∀ j : ℕ, N ^ j * R = d ^ j • (R * N ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_succ, pow_succ' d]
end GlobalTheory.TraceExpSmul
