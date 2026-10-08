-- Prove2me | solution 1 for HarrisEOQ.Lot.economic_lot_size
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:56:26.625259+00:00
-- url     : https://prove2.me/submissions/22015f78-df1a-4c61-850f-c8bc4efca54f

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

set_option autoImplicit false

open HarrisEOQ.Lot

theorem solution (M C S : ℝ) (hM : 0 < M) (hC : 0 < C) (hS : 0 < S) :
    0 < econLotSize M C S ∧
      (∀ X : ℝ, 0 < X → costPerUnit M C S (econLotSize M C S) ≤ costPerUnit M C S X) ∧
      (∀ X : ℝ, 0 < X → costPerUnit M C S X = costPerUnit M C S (econLotSize M C S) →
        X = econLotSize M C S) := by
  have hpos : 0 < 240 * M * S / C := by positivity
  obtain ⟨s, hs_eq⟩ : ∃ s, s = econLotSize M C S := ⟨_, rfl⟩
  rw [← hs_eq]
  have hs : 0 < s := by rw [hs_eq]; exact Real.sqrt_pos.2 hpos
  have hs2 : s ^ 2 = 240 * M * S / C := by rw [hs_eq]; exact Real.sq_sqrt hpos.le
  have hSs : S = C / (240 * M) * s ^ 2 := by rw [hs2]; field_simp
  have key : ∀ X : ℝ, 0 < X →
      costPerUnit M C S X - costPerUnit M C S s = C / (240 * M) * (X - s) ^ 2 / X := by
    intro X hX
    unfold costPerUnit
    rw [hSs]
    field_simp
    ring
  refine ⟨hs, fun X hX => ?_, fun X hX heq => ?_⟩
  · have h1 := key X hX
    have h2 : 0 ≤ C / (240 * M) * (X - s) ^ 2 / X := by positivity
    linarith
  · have h1 := key X hX
    rw [heq, sub_self] at h1
    have h0 : (X - s) ^ 2 = 0 := by
      have h3 : C / (240 * M) * (X - s) ^ 2 / X = 0 := h1.symm
      have h4 : C / (240 * M) * (X - s) ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 h3 with h | h
        · exact h
        · exact absurd h hX.ne'
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h (by positivity)
      · exact h
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h0
    linarith

#print axioms solution
