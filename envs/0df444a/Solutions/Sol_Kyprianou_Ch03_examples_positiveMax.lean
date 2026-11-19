-- Prove2me | solution 1 for Kyprianou.Ch03.examples_positiveMax
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:16:31.116204+00:00
-- url     : https://prove2.me/submissions/98d1573c-5695-4b80-872b-bb238ea5e855

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution :
    IsSubmultiplicative (fun x : ℝ => max x 1) := by
  change (∀ x : ℝ, 0 ≤ max x 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ,
      max (x + y) 1 ≤ c * max x 1 * max y 1
  refine ⟨?_, 2, by norm_num, ?_⟩
  · intro x
    have h : (1 : ℝ) ≤ max x 1 := le_max_right _ _
    linarith
  · intro x y
    have hx : x ≤ max x (1 : ℝ) := le_max_left _ _
    have hy : y ≤ max y (1 : ℝ) := le_max_left _ _
    have hx1 : (1 : ℝ) ≤ max x 1 := le_max_right _ _
    have hy1 : (1 : ℝ) ≤ max y 1 := le_max_right _ _
    have h1 : 0 ≤ max x (1 : ℝ) * (max y 1 - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ max y (1 : ℝ) * (max x 1 - 1) :=
      mul_nonneg (by linarith) (by linarith)
    apply max_le
    · nlinarith
    · nlinarith


