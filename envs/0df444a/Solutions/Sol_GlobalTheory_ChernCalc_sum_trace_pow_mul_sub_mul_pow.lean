-- Prove2me | solution 1 for GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:11.150251+00:00
-- url     : https://prove2.me/submissions/ab70ca4e-9736-4ebf-8e99-70e62424a8d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTracePowMulSubMulPowTelescope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChernCalc
namespace GlobalTheory.ChernCalc
theorem _root_.solution (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by
  have h : ∀ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ (i + 1) * Q ^ (k - (i + 1))).trace - (P ^ i * Q ^ (k - i)).trace := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have e1 : k - 1 - i = k - (i + 1) := by omega
    have e2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [e1, e2, ← Matrix.trace_sub, mul_sub, sub_mul, ← pow_succ, pow_succ' Q, mul_assoc]
  rw [Finset.sum_congr rfl h,
    Finset.sum_range_sub (fun i => (P ^ i * Q ^ (k - i)).trace)]
  simp
end GlobalTheory.ChernCalc
