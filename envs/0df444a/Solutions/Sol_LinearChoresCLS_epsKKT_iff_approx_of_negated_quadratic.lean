-- Prove2me | solution 1 for LinearChoresCLS.epsKKT_iff_approx_of_negated_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:35.94299+00:00
-- url     : https://prove2.me/submissions/947be1d2-0c8f-4605-8c6e-b1a13dc1b290

import Mathlib
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash


theorem solution {n : ℕ} (P P' : Quadratic n)
    (hQ : ∀ i j, P'.Q i j = -P.Q i j) (hc : ∀ i, P'.c i = -P.c i)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Fin n → ℝ) :
    LinearChoresCLS.IsEpsKKT P ε x ↔ ApproxQuadraticKKT P' ε x := by
  have hg (i : Fin n) : sourceGradient P' x i = -sourceGradient P x i := by
    simp only [sourceGradient, hQ, hc, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib,
      neg_add_rev]
    exact add_comm _ _
  rw [ApproxQuadraticKKT]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hε, hx, fun i => ⟨?_, ?_⟩⟩
    · intro hi
      rw [hg]
      by_cases hi1 : x i = 1
      · have hb := (h i).2.2 hi1
        linarith
      · have hlt : x i < 1 := lt_of_le_of_ne (hx i).2 hi1
        have hb := abs_le.mp ((h i).2.1 hi hlt)
        linarith [hb.1]
    · intro hlt
      rw [hg]
      by_cases hi0 : x i = 0
      · have hb := (h i).1 hi0
        linarith
      · have hpos : 0 < x i := lt_of_le_of_ne (hx i).1 (Ne.symm hi0)
        have hb := abs_le.mp ((h i).2.1 hpos hlt)
        linarith [hb.2]
  · rintro ⟨hε', hx, h⟩
    refine ⟨hx, fun i => ⟨?_, ?_, ?_⟩⟩
    · intro hi0
      have hlt : x i < 1 := hi0.symm ▸ zero_lt_one
      have hb := (h i).2 hlt
      rw [hg] at hb
      linarith
    · intro hpos hlt
      have hb1 := (h i).1 hpos
      have hb2 := (h i).2 hlt
      rw [hg] at hb1 hb2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · intro hi1
      have hpos : 0 < x i := hi1.symm ▸ zero_lt_one
      have hb := (h i).1 hpos
      rw [hg] at hb
      linarith
