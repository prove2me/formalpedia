-- Prove2me | solution 1 for MultiPriceOnline.Ratios.explicit_sigma
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:38:30.646974+00:00
-- url     : https://prove2.me/submissions/6619d6a2-a234-4644-a19e-739e5d8a6c9f

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

set_option autoImplicit false
open Finset

theorem solution (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (σ : ℕ → ℝ) (hσ : MultiPriceOnline.Balance.IsBQLimits m r σ) :
    ∀ j ∈ Icc 1 m,
      σ j = (1 - MultiPriceOnline.Hardness.price r (j - 1) / r j) /
        (1 + ∑ j' ∈ Icc 2 m, (1 - r (j' - 1) / r j')) := by
  obtain ⟨hr1, hrm⟩ := hr
  obtain ⟨hσpos, hσsum, hσrel⟩ := hσ
  have hpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hr1
    | succ k hk ih =>
      intro hkm
      have := hrm k hk (by omega)
      linarith [ih (by omega)]
  have hc : ∀ j, 2 ≤ j → j ≤ m → 0 < 1 - r (j - 1) / r j := by
    intro j hj hjm
    have h1 := hrm (j - 1) (by omega) (by omega)
    have e : j - 1 + 1 = j := by omega
    rw [e] at h1
    have h2 := hpos j (by omega) hjm
    rw [sub_pos, div_lt_one h2]
    exact h1
  have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Icc 1 m, f j = f 1 + ∑ j ∈ Icc 2 m, f j := by
    intro f
    have : Icc 1 m = insert 1 (Icc 2 m) := by ext x; simp; omega
    rw [this, Finset.sum_insert (by simp)]
  have hσj : ∀ j ∈ Icc 2 m, σ j = σ 1 * (1 - r (j - 1) / r j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := hσrel j hj.1 hj.2
    have hcj := hc j hj.1 hj.2
    rw [eq_div_iff hcj.ne'] at h
    linarith
  set S : ℝ := ∑ j' ∈ Icc 2 m, (1 - r (j' - 1) / r j') with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun j hj => by
    rw [Finset.mem_Icc] at hj; exact (hc j hj.1 hj.2).le)
  have hden : (1 + S) ≠ 0 := by linarith
  have hsum : σ 1 * (1 + S) = 1 := by
    have := hσsum
    rw [hsplit, Finset.sum_congr rfl hσj, ← Finset.mul_sum] at this
    linarith
  have h1 : σ 1 = 1 / (1 + S) := by
    rw [eq_div_iff hden]; exact hsum
  intro j hj
  rw [Finset.mem_Icc] at hj
  rcases eq_or_lt_of_le hj.1 with h | h
  · subst h
    simp [MultiPriceOnline.Hardness.price, MultiPriceOnline.Balance.pr, h1]
  · have hj2 : 2 ≤ j := h
    rw [hσj j (by rw [Finset.mem_Icc]; exact ⟨hj2, hj.2⟩), h1]
    have : MultiPriceOnline.Hardness.price r (j - 1) = r (j - 1) := by
      simp only [MultiPriceOnline.Hardness.price, MultiPriceOnline.Balance.pr]
      rw [if_neg (by omega)]
    rw [this]
    field_simp
