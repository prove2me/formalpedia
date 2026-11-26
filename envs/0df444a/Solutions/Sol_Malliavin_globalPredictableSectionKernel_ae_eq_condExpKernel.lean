-- Prove2me | solution 1 for Malliavin.globalPredictableSectionKernel_ae_eq_condExpKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:04.991527+00:00
-- url     : https://prove2.me/submissions/fb644916-2742-4ee6-8724-94d54cab7a37

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_Malliavin_KernelIdentification

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      ∀ᵐ w ∂P,
        globalPredictableSectionKernel P (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  filter_upwards [globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos hB hm hgen,
    nonnegativeLebesgueMeasure.ae_ne 0] with t ht ht0
  exact ht (pos_iff_ne_zero.mpr ht0)
end Malliavin
