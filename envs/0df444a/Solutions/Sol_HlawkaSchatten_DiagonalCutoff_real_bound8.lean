-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound8
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:10:45.785831+00:00
-- url     : https://prove2.me/submissions/f179f1b5-1d81-47d5-ac2a-4953298062ae

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_cutoff8

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 8 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n x y z
  have h := (HlawkaSchatten.DiagonalCutoff8.cutoff8 p hp).1 n
    (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  simpa [tripleGap, pairGapSum, pairGap, lpNorm, Pi.add_apply,
    ← Complex.ofReal_add, Complex.norm_real] using h
