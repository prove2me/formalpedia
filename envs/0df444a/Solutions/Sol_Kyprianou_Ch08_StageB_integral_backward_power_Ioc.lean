-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.integral_backward_power_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:58:40.718355+00:00
-- url     : https://prove2.me/submissions/bf9ee53a-45b6-4935-bf05-e8410f70425a

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    (∫ s in Set.Ioc (0 : ℝ) x, (x - s) ^ n ∂volume) =
      x ^ (n + 1) / (n + 1) := by
  calc
    (∫ s in Set.Ioc (0 : ℝ) x, (x - s)^n ∂volume) =
        ∫ s in (0 : ℝ)..x, (x - s)^n :=
          (intervalIntegral.integral_of_le hx).symm
    _ = ∫ t in (x - x)..(x - 0), t^n := by
          simpa only [] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun t : ℝ => t^n) (a := (0 : ℝ)) (b := x) x)
    _ = x^(n+1) / (n+1) := by
          simp [integral_pow]
