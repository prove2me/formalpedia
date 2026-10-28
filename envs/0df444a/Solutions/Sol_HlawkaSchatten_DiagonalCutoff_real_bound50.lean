-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:09:06.40496+00:00
-- url     : https://prove2.me/submissions/54683b11-87e3-499a-addb-d0c778320a96

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_cutoff8

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 50 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n x y z
  have h8 : (8 : ℝ) ≤ p := by linarith
  have h := (HlawkaSchatten.DiagonalCutoff8.cutoff8 p h8).1 n
    (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  simpa [tripleGap, pairGapSum, pairGap, lpNorm, Pi.add_apply,
    ← Complex.ofReal_add, Complex.norm_real] using h
