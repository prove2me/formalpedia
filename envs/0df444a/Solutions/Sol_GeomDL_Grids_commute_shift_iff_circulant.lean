-- Prove2me | solution 1 for GeomDL.Grids.commute_shift_iff_circulant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T15:57:28.534967+00:00
-- url     : https://prove2.me/submissions/dffb69b6-a791-40d5-88a3-cb3278164f39

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix GeomDL.Grids

theorem solution {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (M : Matrix (ZMod n) (ZMod n) R) :
    M * shift R n = shift R n * M ↔ ∃ θ : ZMod n → R, M = circulant θ := by
  have hMS : ∀ i j, (M * shift R n) i j = M i (j + 1) := by
    intro i j
    simp only [shift, mul_apply, circulant_apply]
    rw [Finset.sum_eq_single (j + 1)]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne (by intro h; apply hk; rw [← h]; ring), mul_zero]
    · simp
  have hSM : ∀ i j, (shift R n * M) i j = M (i - 1) j := by
    intro i j
    simp only [shift, mul_apply, circulant_apply]
    rw [Finset.sum_eq_single (i - 1)]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne (by intro h; apply hk; rw [← h]; ring), zero_mul]
    · simp
  constructor
  · intro h
    refine ⟨fun k => M k 0, ?_⟩
    have step : ∀ i j, M i (j + 1) = M (i - 1) j := by
      intro i j
      rw [← hMS, ← hSM, h]
    have key : ∀ (m : ℕ) (i : ZMod n), M i (m : ZMod n) = M (i - m) 0 := by
      intro m
      induction m with
      | zero => intro i; simp
      | succ m ih =>
        intro i
        push_cast
        rw [step, ih]
        congr 1
        ring
    ext i j
    rw [circulant_apply, ← ZMod.natCast_zmod_val j, key]
  · rintro ⟨θ, rfl⟩
    exact circulant_mul_comm θ _
