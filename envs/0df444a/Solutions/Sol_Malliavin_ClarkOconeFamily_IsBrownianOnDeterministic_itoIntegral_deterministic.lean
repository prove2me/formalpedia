-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:13.103265+00:00
-- url     : https://prove2.me/submissions/1dd588d4-0150-4750-bea1-16b49b966739

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_deterministicIntegral_apply
import Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_deterministicIntegral_eq_wienerIntegral

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
    (hC : C.IsBrownianOnDeterministic) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) =
      wienerIntegral C.isPreBrownian f := by
  rw [← C.deterministicIntegral_apply, hC.deterministicIntegral_eq_wienerIntegral]
end ClarkOconeFamily.IsBrownianOnDeterministic
end Malliavin
