-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:49.489842+00:00
-- url     : https://prove2.me/submissions/e72ab671-6f81-4d3c-86ec-3a9b0ab33862

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_itoIntegral_deterministic
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc


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
namespace ClarkOconeFamily.IsBrownianOnDeterministic
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) {a b : ℝ≥0} (hab : a ≤ b) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by
  rw [hC.itoIntegral_deterministic,
    wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab]
end ClarkOconeFamily.IsBrownianOnDeterministic
end Malliavin
