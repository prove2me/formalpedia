-- Prove2me | solution 1 for Malliavin.naturalItoIntegral_deterministic_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:04.57782+00:00
-- url     : https://prove2.me/submissions/f263876b-6c1a-448e-a1fc-4636f549ef72

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_naturalItoIntegral_deterministic
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc


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
    {a b : ℝ≥0} (hab : a ≤ b) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp hB b - brownianLp hB a := by
  rw [naturalItoIntegral_deterministic,
    wienerIntegral_indicatorConstLp_Ioc hB hab]
end Malliavin
