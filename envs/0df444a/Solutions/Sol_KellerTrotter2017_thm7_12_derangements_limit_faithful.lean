-- Prove2me | solution 1 for KellerTrotter2017.thm7_12_derangements_limit_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:59:19.582731+00:00
-- url     : https://prove2.me/submissions/6dffb00b-0412-45c6-99ca-4d9632057b6d

import Mathlib

theorem solution :
    Filter.Tendsto
      (fun n : ℕ => (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ x, σ x ≠ x} : ℝ) / (n.factorial : ℝ))
      Filter.atTop (nhds (Real.exp (-1))) := by
  have h : ∀ n : ℕ, Fintype.card {σ : Equiv.Perm (Fin n) // ∀ x, σ x ≠ x} = numDerangements n := by
    intro n
    rw [← card_derangements_fin_eq_numDerangements]
    exact Fintype.card_congr (Equiv.refl _)
  simp_rw [h]
  exact numDerangements_tendsto_inv_e
