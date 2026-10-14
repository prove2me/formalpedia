-- Prove2me | solution 1 for GenericBudgets.MaximinShare.total_price_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:09:21.398306+00:00
-- url     : https://prove2.me/submissions/521b023c-86b6-47bd-8856-c82e05af08b9

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

open GenericBudgets.MaximinShare

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (b : Fin n → ℝ) (σ : Fin m → Fin n) (p : Fin m → ℝ)
    (hCE : IsCE v b σ p) : GenericBudgets.AlmostEqual.price p Finset.univ ≤ ∑ i, b i := by
  classical
  have hs : GenericBudgets.AlmostEqual.price p Finset.univ =
      ∑ i, GenericBudgets.AlmostEqual.price p (bundle σ i) := by
    simp only [GenericBudgets.AlmostEqual.price, bundle, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [hs]
  exact Finset.sum_le_sum fun i _ => (hCE.2 i).1
