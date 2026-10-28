-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound6
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:17:13.220675+00:00
-- url     : https://prove2.me/submissions/d6e63243-c559-4db8-a6c3-ba385c5e5670

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_cutoff6

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 6 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n x y z
  have h := (HlawkaSchatten.DiagonalCutoff6.cutoff6 p hp).1 n
    (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  simpa [tripleGap, pairGapSum, pairGap, lpNorm, Pi.add_apply,
    ← Complex.ofReal_add, Complex.norm_real] using h
