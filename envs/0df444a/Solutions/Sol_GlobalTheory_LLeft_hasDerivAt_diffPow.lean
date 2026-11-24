-- Prove2me | solution 1 for GlobalTheory.LLeft.hasDerivAt_diffPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:33.098952+00:00
-- url     : https://prove2.me/submissions/f48fb202-ef00-497b-af4c-72246333f8f9

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
theorem _root_.solution (k : ℕ) (s : ℂ) : ∀ x : ℝ, 0 < x →
    HasDerivAt (diffPow k s) (-s * diffPow k (s + 1) x) x := by
  induction k with
  | zero =>
    intro x hx
    by_cases hs : s = 0
    · subst hs
      have : diffPow 0 0 = fun _ => (1 : ℂ) := by
        funext y; simp [diffPow]
      rw [this]
      simpa using hasDerivAt_const x (1 : ℂ)
    · have h := hasDerivAt_ofReal_cpow_const hx.ne' (r := -s) (neg_ne_zero.mpr hs)
      have e : -s - 1 = -(s + 1) := by ring
      rw [e] at h
      exact h
  | succ k ih =>
    intro x hx
    have h1 := ih x hx
    have h2 := (ih (x + 1) (by linarith)).comp_add_const x 1
    have h3 := h1.sub h2
    have e : -s * diffPow (k + 1) (s + 1) x
        = -s * diffPow k (s + 1) x - -s * diffPow k (s + 1) (x + 1) := by
      simp only [diffPow]; ring
    rw [e]
    exact h3
end GlobalTheory.LLeft
