-- Prove2me | solution 1 for Kyprianou.Ch03.examples_absoluteMaxPower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:23:59.270582+00:00
-- url     : https://prove2.me/submissions/c30678a6-2561-4ab9-8da1-6176ec2cea8d

import Theorems.Thm_Kyprianou_Ch03_examples_absoluteMax
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
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max |x| 1) ^ alpha)) := by
  intro alpha halpha
  rcases Kyprianou.Ch03.examples_absoluteMax with
    ⟨hnonneg, c, hc, hmul⟩
  change (∀ x : ℝ, 0 ≤ (max |x| 1) ^ alpha) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : ℝ,
        (max |x + y| 1) ^ alpha ≤
          C * (max |x| 1) ^ alpha * (max |y| 1) ^ alpha
  refine ⟨?_, c ^ alpha, Real.rpow_pos_of_pos hc _, ?_⟩
  · intro x
    exact Real.rpow_nonneg (hnonneg x) _
  · intro x y
    have hx := hnonneg x
    have hy := hnonneg y
    calc
      (max |x + y| 1) ^ alpha ≤
          (c * max |x| 1 * max |y| 1) ^ alpha :=
        Real.rpow_le_rpow (hnonneg (x + y)) (hmul x y) (le_of_lt halpha)
      _ = c ^ alpha * (max |x| 1) ^ alpha * (max |y| 1) ^ alpha := by
        rw [Real.mul_rpow (mul_nonneg (le_of_lt hc) hx) hy,
          Real.mul_rpow (le_of_lt hc) hx]


