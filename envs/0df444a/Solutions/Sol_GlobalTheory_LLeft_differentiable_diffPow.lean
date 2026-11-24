-- Prove2me | solution 1 for GlobalTheory.LLeft.differentiable_diffPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:32.270977+00:00
-- url     : https://prove2.me/submissions/f6d3c529-b1d1-4d90-9c66-afd2ead29657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (k : ℕ) : ∀ x : ℝ, 0 < x →
    Differentiable ℂ (fun s => diffPow k s x) := by
  induction k with
  | zero =>
    intro x hx
    simp only [diffPow]
    exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  | succ k ih =>
    intro x hx
    simp only [diffPow]
    exact (ih x hx).sub (ih (x + 1) (by linarith))
end GlobalTheory.LLeft
