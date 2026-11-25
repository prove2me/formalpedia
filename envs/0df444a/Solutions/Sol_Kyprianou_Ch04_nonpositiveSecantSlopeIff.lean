-- Prove2me | solution 1 for Kyprianou.Ch04.nonpositiveSecantSlopeIff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:34:15.270973+00:00
-- url     : https://prove2.me/submissions/6ae41d6f-a985-4e7c-9b9c-591558378eea

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Convex.Function
open Set
set_option autoImplicit false
theorem solution
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) :
    let m := max 0 (sInf ((fun x : ℝ => f x / x) '' Set.Ioi 0))
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < x ∧ f x < ε * x) ↔ m = 0 := by
  dsimp only
  let S : Set ℝ := (fun x : ℝ => f x / x) '' Ioi 0
  change (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < x ∧ f x < ε * x) ↔
    max 0 (sInf S) = 0
  constructor
  · intro h
    apply max_eq_left
    by_contra! hn
    obtain ⟨x, hx, hfx⟩ := h (sInf S) hn
    by_cases hb : BddBelow S
    · exact (not_lt_of_ge (csInf_le hb ⟨x, hx, rfl⟩)) ((div_lt_iff₀ hx).2 hfx)
    · exact (not_lt_of_ge (by rw [Real.sInf_of_not_bddBelow hb])) hn
  · intro hm ε hε
    by_contra! hn
    have hl : ∀ y ∈ S, ε ≤ y := by
      rintro y ⟨x, hx, rfl⟩
      exact (le_div_iff₀ hx).2 (hn x hx)
    have hne : S.Nonempty := ⟨f 1 / 1, 1, by norm_num, rfl⟩
    have hh : ε ≤ sInf S := le_csInf hne hl
    linarith [le_max_right 0 (sInf S)]
