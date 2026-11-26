-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_finite_cap_selector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:23.289081+00:00
-- url     : https://prove2.me/submissions/322f3374-6c5c-43cc-9494-b8e743e5c613

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite representative agrees with the cap on the finite event and gives the capped extended clock. -/
theorem solution
    {Ω : Type} (τ : Ω → WithTop NNReal) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, τ w ≠ ⊤ → τ w = (finiteTime w : WithTop NNReal))
    (n : NNReal) :
    let T : Ω → NNReal := fun w => if τ w ≤ (n : WithTop NNReal) then finiteTime w else n
    (∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal)) := by
  intro T w
  by_cases h : τ w ≤ (n : WithTop NNReal)
  · have hf : τ w ≠ ⊤ := ne_of_lt (h.trans_lt (WithTop.coe_lt_top n))
    rw [min_eq_left h, hfin w hf]
    simp only [T, if_pos h]
  · rw [min_eq_right (le_of_not_ge h)]
    simp only [T, if_neg h]
