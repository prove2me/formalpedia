-- Prove2me | solution 1 for Malliavin.map_naturalItoIntegral_deterministic_eq_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:07.591851+00:00
-- url     : https://prove2.me/submissions/f608cf51-9178-433a-adf0-1114d73c6e66

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_naturalItoIntegral_deterministic
import Theorems.Thm_Malliavin_map_wienerIntegral_eq_gaussianReal


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
    P.map (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding 𝓅 f)) =
        gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [naturalItoIntegral_deterministic,
    map_wienerIntegral_eq_gaussianReal]
end Malliavin
