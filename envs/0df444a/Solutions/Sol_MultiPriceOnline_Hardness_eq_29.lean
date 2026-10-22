-- Prove2me | solution 1 for MultiPriceOnline.Hardness.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:01:59.057738+00:00
-- url     : https://prove2.me/submissions/80ca437f-7931-4840-b9ff-418395518c6b

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
set_option autoImplicit false
open Finset MultiPriceOnline.Hardness

theorem solution {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    (B : ℕ → ℝ) (n k : ℕ) :
    (n : ℝ) * k * ∑ l ∈ Icc 1 m, r l * B l * (1 - Real.exp (-α l)) =
      (1 - Real.exp (-α 1)) * ∑ l ∈ Icc 1 m, (price r l - price r (l - 1)) * B l * n * k := by
  obtain ⟨hr1, hrinc⟩ := hr
  obtain ⟨_, _, hrel⟩ := hα
  have hpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hr1
    | succ j hj ih =>
      intro hjm
      exact lt_trans (ih (by omega)) (hrinc j hj (by omega))
  have key : ∀ l ∈ Icc 1 m, r l * (1 - Real.exp (-α l)) = (1 - Real.exp (-α 1)) * (price r l - price r (l - 1)) := by
    intro l hl
    rw [mem_Icc] at hl
    unfold price MultiPriceOnline.Balance.pr
    by_cases h1 : l = 1
    · subst h1; simp; ring
    · have hl2 : 2 ≤ l := by omega
      have hl0 : l ≠ 0 := by omega
      have hl1 : l - 1 ≠ 0 := by omega
      simp only [if_neg hl0, if_neg hl1]
      have hrl := hpos l hl.1 hl.2
      have hlt : r (l - 1) < r l := by
        have := hrinc (l - 1) (by omega) (by omega)
        rwa [show l - 1 + 1 = l by omega] at this
      have hden : 0 < 1 - r (l - 1) / r l := by
        rw [sub_pos, div_lt_one hrl]; exact hlt
      have := hrel l hl2 hl.2
      rw [eq_div_iff hden.ne'] at this
      have e2 : (1 - r (l - 1) / r l) * r l = r l - r (l - 1) := by field_simp
      calc r l * (1 - Real.exp (-α l)) = r l * ((1 - Real.exp (-α 1)) * (1 - r (l - 1) / r l)) := by rw [this]
        _ = (1 - Real.exp (-α 1)) * ((1 - r (l - 1) / r l) * r l) := by ring
        _ = _ := by rw [e2]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have := key l hl
  calc (n:ℝ) * k * (r l * B l * (1 - Real.exp (-α l))) = (n:ℝ) * k * B l * (r l * (1 - Real.exp (-α l))) := by ring
    _ = (n:ℝ) * k * B l * ((1 - Real.exp (-α 1)) * (price r l - price r (l - 1))) := by rw [this]
    _ = _ := by ring
