-- Prove2me | solution 2 for Kyprianou.Ch01.inverseGaussianFirstPassageLaplaceRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:18:29.315105+00:00
-- url     : https://prove2.me/submissions/552c7c5a-8944-49e6-8df0-c8ef1ca71bdd

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageNaturalRightStoppingContinuousV2
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    IsNaturalRightStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  constructor
  · exact firstUpperPassageNaturalRightStoppingContinuousV2
      X hXmeas hAllContinuous s hs
  · intro q hq
    rcases lt_or_eq_of_le hq with hpos | hzero
    · have hformula := (brownianDiscountedUpperPassage
        P X 1 b q s (by norm_num) hpos hs hB hXmeas).2
      simpa [one_pow, one_mul, mul_one, div_one, neg_mul] using hformula
    · have hq0 : q = 0 := hzero.symm
      subst q
      have hz := (inverseGaussianZeroDiscountPositiveDrift
        P X b s hb hs hB hXmeas).2
      simpa [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hz
