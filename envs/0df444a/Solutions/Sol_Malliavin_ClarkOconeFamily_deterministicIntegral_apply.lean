-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.deterministicIntegral_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:14:29.203047+00:00
-- url     : https://prove2.me/submissions/7ffdc593-8d38-45d5-bdc1-dbc2b3014838

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.deterministicIntegral f =
      C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) := rfl
end ClarkOconeFamily
end Malliavin
