-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstPassageLaplace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:42:28.759899+00:00
-- url     : https://prove2.me/submissions/0c3647a9-a168-4c05-a190-d88aa4a7f91e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageNaturalStoppingContinuous
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The inverse-Gaussian transform follows from the Brownian upper passage
    identity, its q=0 positive-drift limit, and adapted hitting-time measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    IsNaturalStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  refine ⟨Kyprianou.Ch01.firstUpperPassageNaturalStoppingContinuous
    X hXmeas hAllContinuous s hs, ?_⟩
  intro q hq
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    have hz := Kyprianou.Ch01.inverseGaussianZeroDiscountPositiveDrift
      P X b s hb hs hB hXmeas
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hz.2
  · have hp := Kyprianou.Ch01.brownianDiscountedUpperPassage
      P X 1 b q s (by norm_num) hpos hs hB hXmeas
    simpa [pow_two] using hp.2
