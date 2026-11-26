-- Prove2me | solution 1 for Malliavin.hasGaussianLaw_naturalItoIntegral_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:06.953879+00:00
-- url     : https://prove2.me/submissions/72f2ccf2-e176-49a0-9211-58b22721e6e1

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_naturalItoIntegral_deterministic
import Theorems.Thm_Malliavin_hasGaussianLaw_wienerIntegral


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
    HasGaussianLaw
      (naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 f) : W → ℝ) P := by
  rw [naturalItoIntegral_deterministic]
  exact hasGaussianLaw_wienerIntegral hB f
end Malliavin
