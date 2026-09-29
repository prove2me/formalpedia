-- Prove2me | solution 1 for Gilbreath.propagation
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T19:18:26.375321+00:00
-- url     : https://prove2.me/submissions/c75abaee-8b31-4dfc-924b-ec8575cb2cfa

import Definitions.Def_gilbreath_triangle

open Gilbreath

theorem solution (a : ℕ → ℕ) (m : ℕ) (h0 : a 0 = 1)
    (h : ∀ n, 1 ≤ n → n ≤ m → a n = 0 ∨ a n = 2) (j : ℕ) (hj : j ≤ m) :
    iterAbsDiff a j 0 = 1 := by
  induction j generalizing a m with
  | zero => simpa using h0
  | succ j ih =>
    have hm : 1 ≤ m := le_trans (Nat.succ_le_succ (Nat.zero_le j)) hj
    rw [iterAbsDiff_succ']
    refine ih (absDiff a) (m - 1) ?_ ?_ (by omega)
    · have h1 := h 1 le_rfl hm
      have h0' : (a 0 : ℤ) = 1 := by exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) h0
      rcases h1 with h1 | h1 <;> simp [absDiff, h1, h0']
    · intro n hn hnm
      have hn1 : a n = 0 ∨ a n = 2 := h n hn (by omega)
      have hn2 : a (n + 1) = 0 ∨ a (n + 1) = 2 := h (n + 1) (by omega) (by omega)
      rcases hn1 with h1 | h1 <;> rcases hn2 with h2 | h2 <;>
        simp [absDiff, h1, h2]
