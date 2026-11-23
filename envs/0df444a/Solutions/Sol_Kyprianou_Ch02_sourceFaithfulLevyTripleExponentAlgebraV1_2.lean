-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:04:42.516278+00:00
-- url     : https://prove2.me/submissions/b37bb1c5-ea6a-4f29-9a7f-91a5f2b56ced

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_ProbabilityTheory_integral_levyCompensatedIntegrand_eq_small_add_large
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure] :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      (Complex.exp ((((t : ℝ) : ℂ)) *
          (-Complex.I * (a : ℂ) * (ξ : ℂ) -
            (((σ : ℝ) ^ 2 * ξ ^ 2 / 2 : ℝ) : ℂ)))) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | 1 ≤ |x|},
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) = (Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) := by
  intro t ξ
  have hlarge :
      (∫ x in {x : ℝ | 1 ≤ |x|},
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure) =
      (∫ x in {x : ℝ | 1 ≤ |x|},
        (Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1) ∂levyMeasure) := by
    apply setIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
    intro x hx
    congr 1
    push_cast
    ring
  have hsmall :
      (∫ x in Set.Ioo (-1 : ℝ) 1,
        ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) =
      (∫ x in Set.Ioo (-1 : ℝ) 1,
        (Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1 -
          (x : ℂ) * (ξ : ℂ) * Complex.I) ∂levyMeasure) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hnorm : |x| < (1 : ℝ) := abs_lt.mpr hx
    simp only [ProbabilityTheory.levyCompensatedIntegrand, hnorm, if_true, mul_one]
  have hsplit :=
    ProbabilityTheory.integral_levyCompensatedIntegrand_eq_small_add_large
      hlevyMeasure ξ
  rw [hlarge, hsmall]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold Kyprianou.Ch01.levyTripleExponent
  dsimp only
  rw [hsplit]
  push_cast
  ring
