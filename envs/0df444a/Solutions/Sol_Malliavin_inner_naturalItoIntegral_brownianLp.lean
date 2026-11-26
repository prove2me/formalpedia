-- Prove2me | solution 1 for Malliavin.inner_naturalItoIntegral_brownianLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:33.4561+00:00
-- url     : https://prove2.me/submissions/0406f1e4-47a2-4966-97e0-8bd1693ffd8e

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_inner_naturalItoIntegral_wienerIntegral
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
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P) (t : ℝ≥0) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (brownianLp hB t) =
      inner ℝ U
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) := by
  rw [← wienerIntegral_intervalIndicator hB t]
  exact inner_naturalItoIntegral_wienerIntegral hB hsm hnat U (intervalIndicator t)
end Malliavin
