-- Prove2me | solution 1 for GlobalTheory.ExpPow.int_eq_zero_of_exp_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:49.71913+00:00
-- url     : https://prove2.me/submissions/c48aaf3a-b186-484f-a7a9-f95b43d99499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PowExpIOrInvInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExpPow
namespace GlobalTheory.ExpPow
theorem _root_.solution (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : (m : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  by_contra hm
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hm (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨(m : ℚ) / (2 * n), ?_⟩
  push_cast
  rw [h1]
  field_simp
end GlobalTheory.ExpPow
