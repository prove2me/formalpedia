-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:18:37.507194+00:00
-- url     : https://prove2.me/submissions/540529a6-8f9a-45f9-ac02-7d4b0911a912

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff16

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 16 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n x y z
  have h := (HlawkaSchatten.DiagonalCutoff.cutoff16 p hp).1 n
    (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  simpa [tripleGap, pairGapSum, pairGap, lpNorm, Pi.add_apply,
    ← Complex.ofReal_add, Complex.norm_real] using h

#print axioms solution
