-- Prove2me | solution 1 for Malliavin.toLp_integral_globalPredictableSectionKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:24.54245+00:00
-- url     : https://prove2.me/submissions/17805928-bbd2-49d2-8aba-ca38dcb48578

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
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    (memLp_integral_globalPredictableSectionKernel hB hm hgen U).toLp _
      = (predictableProjection (Filtration.natural B hm) U : TimeProcessL2 P) := by
  apply Lp.ext
  refine (MemLp.coeFn_toLp _).trans ?_
  exact (predictableProjection_ae_eq_integral_globalPredictableSectionKernel hB hm hgen U).symm
end Malliavin
