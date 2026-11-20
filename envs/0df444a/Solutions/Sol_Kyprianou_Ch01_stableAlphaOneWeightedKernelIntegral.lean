-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneWeightedKernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:37:26.661844+00:00
-- url     : https://prove2.me/submissions/23e60828-186c-49eb-a75f-e1c2a15258c0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveWeightedJumpKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (c xi : ℝ) :
    -(∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (c : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by
  calc
    -(∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        -((c * r ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r) ∂volume := by
        rw [integral_neg]
    _ = ∫ r in Set.Ioi (0 : ℝ),
        (c : ℂ) * (((1 : ℂ) -
          Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
          Complex.I * (((xi * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      convert congrArg Neg.neg
        (Kyprianou.Ch01.stableAlphaOnePositiveWeightedJumpKernel
          c xi r hr) using 1 <;> ring
    _ = _ := by rw [integral_const_mul]
