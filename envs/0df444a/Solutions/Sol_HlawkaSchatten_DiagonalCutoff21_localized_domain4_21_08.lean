-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_08
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:12:48.0198+00:00
-- url     : https://prove2.me/submissions/69f8b2d2-d500-4d89-8935-fc54eefd029f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain2_21_08_part0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain2_21_08_part1
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (22 : ℝ) ≤ p → p ≤ (177/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  intro p hp hpmax X hd ho hS hT hG
  rcases le_total p (353/16 : ℝ) with hl | hr
  ·
    exact HlawkaSchatten.DiagonalCutoff21.localized_domain2_21_08_part0 p (by linarith) (by linarith) X hd ho hS hT hG
  ·
    exact HlawkaSchatten.DiagonalCutoff21.localized_domain2_21_08_part1 p (by linarith) (by linarith) X hd ho hS hT hG

#print axioms solution
