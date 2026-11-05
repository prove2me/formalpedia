-- Prove2me | solution 1 for LL_Decomp1526a.card_evenBlock_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:11.66321+00:00
-- url     : https://prove2.me/submissions/ea1bb762-d3b6-46a4-836b-b0388c6f9d65

import Mathlib
import Definitions.Def_LL_Decomp1526a_evenBlock

open Finset Real
open scoped Chebyshev Classical

theorem solution {X : ℝ} (hX : 0 ≤ X) :
    (#(LL_Decomp1526a.evenBlock X) : ℝ) ≤ X / 2 + 1 := by
  set a := ⌊X⌋₊ with ha
  set b := ⌊2 * X⌋₊ with hb
  have hab : a ≤ b := Nat.floor_le_floor (by linarith)
  have hcard : #(LL_Decomp1526a.evenBlock X) + a / 2 = b / 2 := by
    have h1 : (Ioc 0 b).filter (fun x => 2 ∣ x) =
        (Ioc 0 a).filter (fun x => 2 ∣ x) ∪ (Ioc a b).filter (fun x => 2 ∣ x) := by
      rw [← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
    have h2 : Disjoint ((Ioc 0 a).filter (fun x => 2 ∣ x)) ((Ioc a b).filter (fun x => 2 ∣ x)) :=
      disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl)
    have h3 := Nat.Ioc_filter_dvd_card_eq_div b 2
    have h4 := Nat.Ioc_filter_dvd_card_eq_div a 2
    rw [h1, card_union_of_disjoint h2, h4] at h3
    have : LL_Decomp1526a.evenBlock X = (Ioc a b).filter (fun x => 2 ∣ x) := by
      unfold LL_Decomp1526a.evenBlock
      simp only [even_iff_two_dvd]
      rfl
    rw [this]; omega
  have h5 : b / 2 = ⌊X⌋₊ := by
    have := Nat.floor_div_natCast (2 * X) 2
    rw [show 2 * X / ((2 : ℕ) : ℝ) = X by push_cast; ring] at this
    rw [hb, ← this]
  have h6 : a / 2 = ⌊X / 2⌋₊ := by
    have := Nat.floor_div_natCast X 2
    rw [ha, ← this]; push_cast; rfl
  have h7 : (b / 2 : ℕ) ≤ X := by rw [h5]; exact Nat.floor_le hX
  have h8 : X / 2 < (a / 2 : ℕ) + 1 := by rw [h6]; exact Nat.lt_floor_add_one _
  have h9 : ((#(LL_Decomp1526a.evenBlock X) : ℕ) : ℝ) + (a / 2 : ℕ) = (b / 2 : ℕ) := by
    exact_mod_cast hcard
  linarith
