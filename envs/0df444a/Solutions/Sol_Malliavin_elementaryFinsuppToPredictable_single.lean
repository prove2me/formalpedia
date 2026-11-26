-- Prove2me | solution 1 for Malliavin.elementaryFinsuppToPredictable_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:48.675089+00:00
-- url     : https://prove2.me/submissions/414babf1-5f6d-45c4-8dc4-8b4911323940

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToPredictable 𝓕 P (Finsupp.single x c) =
      c • elementaryPredictableGenerator 𝓕 P x :=
  Finsupp.linearCombination_single _ _ _
end Malliavin
