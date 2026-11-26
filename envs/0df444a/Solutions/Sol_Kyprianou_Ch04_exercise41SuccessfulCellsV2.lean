-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SuccessfulCellsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:33:04.032323+00:00
-- url     : https://prove2.me/submissions/999f1c77-7a62-482e-9c71-776fd4658e99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulGapV1
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellCardV1
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem solution
    (A : Finset ℕ) (τ v : ℕ → ℝ) (a h d : ℝ)
    (hh : 0 < h) (hd : 0 < d)
    (hcell : ∀ i ∈ A, a + (i : ℝ) * h ≤ τ i ∧
      τ i < a + ((i : ℝ) + 1) * h)
    (hnear : ∀ i ∈ A, |v i| < d * h / 8)
    (hslope : ∀ i ∈ A, ∀ j ∈ A, i < j →
      d / 2 * (τ j - τ i) ≤ v j - v i) :
    A.card ≤ 2 := by
  apply exercise41SuccessfulCellCardV1 A τ a h hh hcell
  intro i hi j hj hij
  exact exercise41SuccessfulGapV1 d h (v i) (v j)
    (τ j - τ i) hd hh (hnear i hi) (hnear j hj)
    (hslope i hi j hj hij)
