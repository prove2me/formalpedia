-- Prove2me | solution 1 for LocalDOvS.SUS.eq_EC_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:01:38.965723+00:00
-- url     : https://prove2.me/submissions/0eecef5e-30d5-4f5b-b821-84315e1043ac

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

theorem solution (S : Finset ℕ) (f m hw : ℕ → ℝ) (ε : ℝ)
    (hdev : ∀ x ∈ S, |f x - m x| ≤ hw x)
    (hhw : ∀ x ∈ S, hw x ≤ (S.card : ℝ) * ε / 80)
    (hnoI : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ (m x + hw x ≤ m y - hw y)) :
    ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ (S.card : ℝ) / 20 * ε := by
  intro x hx y hy
  have hwx_nonneg : 0 ≤ hw x := le_trans (abs_nonneg _) (hdev x hx)
  have hwy_nonneg : 0 ≤ hw y := le_trans (abs_nonneg _) (hdev y hy)
  have hwx_bd := hhw x hx
  have hwy_bd := hhw y hy
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    linarith
  · have h1 : m y - hw y < m x + hw x := not_le.mp (hnoI x hx y hy hxy)
    have h2 : m x - hw x < m y + hw y := not_le.mp (hnoI y hy x hx (Ne.symm hxy))
    have hdx := abs_le.mp (hdev x hx)
    have hdy := abs_le.mp (hdev y hy)
    rw [abs_le]
    constructor <;> linarith
