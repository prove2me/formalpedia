-- Prove2me | solution 1 for GlobalTheory.T.window_around_last_max_null_sequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:50:42.844875+00:00
-- url     : https://prove2.me/submissions/87a9d6ab-91dc-44fe-a603-a60e0dd66789

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAroundLastMaxNullSequence
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAroundLastMaxNullSequenceStatement
import Theorems.Thm_GlobalTheory_window_around_last_max


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  first | exact @GlobalTheory.window_around_last_max | exact GlobalTheory.window_around_last_max | (intros; apply GlobalTheory.window_around_last_max <;> assumption)
end _root_.GlobalTheory.T
