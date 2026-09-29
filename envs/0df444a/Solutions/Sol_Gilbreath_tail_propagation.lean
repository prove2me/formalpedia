-- Prove2me | solution 1 for Gilbreath.tail_propagation
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T20:32:55.965429+00:00
-- url     : https://prove2.me/submissions/c901c498-9d48-4b09-8261-6df62bda4459

import Definitions.Def_gilbreath_triangle

open Gilbreath

theorem solution (a : ℕ → ℕ) (j : ℕ)
    (h : ∀ n, 1 ≤ n → n ≤ j + 1 → a n = 0 ∨ a n = 2) :
    iterAbsDiff a j 1 = 0 ∨ iterAbsDiff a j 1 = 2 := by
  induction j generalizing a with
  | zero => simpa using h 1 le_rfl le_rfl
  | succ j ih =>
    -- Peel the first difference off the front: `Δ^{j+1} a = Δ^j (Δ a)`.
    rw [iterAbsDiff_succ']
    refine ih (absDiff a) ?_
    -- `{0, 2}` is closed under absolute differences, so the block shortens by one
    -- index but survives in `Δ a`.
    intro n hn hnj
    have h1 := h n hn (by omega)
    have h2 := h (n + 1) (by omega) (by omega)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [absDiff, h1, h2]
