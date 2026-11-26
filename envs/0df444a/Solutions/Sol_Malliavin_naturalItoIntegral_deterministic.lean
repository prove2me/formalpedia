-- Prove2me | solution 1 for Malliavin.naturalItoIntegral_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:47.134289+00:00
-- url     : https://prove2.me/submissions/f7cd419d-2fc5-44f5-972d-93f4b07b78cc

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅 f) =
      wienerIntegral hB f := by
  rw [← naturalItoDeterministicIntegral_apply,
    naturalItoDeterministicIntegral_eq_wienerIntegral]
end Malliavin
