-- Prove2me | solution 1 for Malliavin.elementaryFinsuppToBrownian_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:49.414283+00:00
-- url     : https://prove2.me/submissions/cedcf4ac-beed-437d-932f-c3e4c25ec9d1

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
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToBrownian hB hsm hnat (Finsupp.single x c) =
      c • elementaryBrownianGenerator hB hsm hnat x :=
  Finsupp.linearCombination_single _ _ _
end Malliavin
