-- Prove2me | solution 1 for GeomDL.Grids.shift_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:33:56.868624+00:00
-- url     : https://prove2.me/submissions/916d6c29-ab4c-45bb-8141-2e3942570267

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open GeomDL.Grids Matrix

theorem solution {R : Type*} [CommRing R] {n : ℕ} [NeZero n] :
    (∀ (x : ZMod n → R) (u : ZMod n), ((shift R n)ᵀ *ᵥ x) u = x (u + 1)) ∧
      (shift R n)ᵀ * shift R n = 1 ∧ shift R n * (shift R n)ᵀ = 1 := by
  have key : ∀ a b : ZMod n, (shift R n) a b = if a = b + 1 then 1 else 0 := by
    intro a b
    simp only [shift, circulant_apply, Pi.single_apply, sub_eq_iff_eq_add, add_comm (1 : ZMod n) b]
  refine ⟨fun x u => ?_, ?_, ?_⟩
  · simp only [mulVec, dotProduct, transpose_apply, key, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (u + 1)]
    simp
  · ext i j
    simp only [mul_apply, transpose_apply, key, mul_ite, mul_one, mul_zero, one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro b _
        split_ifs with h1 h2 <;> try rfl
        exact absurd (add_right_cancel (h1.symm.trans h2)).symm h
  · ext i j
    simp only [mul_apply, transpose_apply, key, mul_ite, mul_one, mul_zero, one_apply]
    by_cases h : i = j
    · subst h
      rw [Finset.sum_eq_single (i - 1)]
      · simp
      · intro b _ hb; simp [eq_sub_iff_add_eq.symm, hb]
        intro h1; exact absurd (by rw [h1]; ring) hb
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro b _
        split_ifs with h1 h2 <;> try rfl
        exact absurd (h1.trans h2.symm).symm h
