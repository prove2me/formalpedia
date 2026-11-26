-- Prove2me | solution 1 for Malliavin.naturalItoIntegral_deterministic_intervalIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:49.846802+00:00
-- url     : https://prove2.me/submissions/53c597f7-5ac6-43bf-bcea-b3307099ea5c

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_naturalItoIntegral_deterministic
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator


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
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) =
      brownianLp hB t := by
  rw [naturalItoIntegral_deterministic, wienerIntegral_intervalIndicator]
end Malliavin
