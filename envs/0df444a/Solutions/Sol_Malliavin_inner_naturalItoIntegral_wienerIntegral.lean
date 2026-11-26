-- Prove2me | solution 1 for Malliavin.inner_naturalItoIntegral_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:24.89903+00:00
-- url     : https://prove2.me/submissions/1f595a1d-5b11-43e6-8078-dbbe17fb4e72

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_naturalItoIntegral_deterministic

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
    (U : PredictableProcessL2 𝓅 P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (wienerIntegral hB f) =
      inner ℝ U (deterministicPredictableEmbedding 𝓅 f) := by
  rw [← naturalItoIntegral_deterministic hB hsm hnat f]
  exact inner_naturalItoIntegral hB hsm hnat U _
end Malliavin
