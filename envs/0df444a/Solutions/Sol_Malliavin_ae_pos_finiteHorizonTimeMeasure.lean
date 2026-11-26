-- Prove2me | solution 1 for Malliavin.ae_pos_finiteHorizonTimeMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:31.765988+00:00
-- url     : https://prove2.me/submissions/f7bc32a5-6f1a-4701-9bf7-c046487e35d1

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
theorem _root_.solution (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t := by
  have hne : ∀ᵐ t ∂finiteHorizonTimeMeasure T, t ≠ 0 := by
    exact ae_restrict_of_ae (nonnegativeLebesgueMeasure.ae_ne 0)
  filter_upwards [hne] with t ht
  exact pos_iff_ne_zero.mpr ht
end Malliavin
