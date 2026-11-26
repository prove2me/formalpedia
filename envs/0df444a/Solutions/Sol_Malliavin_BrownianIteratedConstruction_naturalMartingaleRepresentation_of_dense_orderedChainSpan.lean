-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_dense_orderedChainSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:04.189384+00:00
-- url     : https://prove2.me/submissions/4b44645e-6a2f-49d5-a694-18c66084d810

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianChaosTotal_iff_dense_orderedChainSpan
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_brownianChaosTotal


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hdense : Dense (brownianOrderedChainSpan hB : Set (RandomL2 P))) :
    NaturalMartingaleRepresentation hB hsm hnat :=
  naturalMartingaleRepresentation_of_brownianChaosTotal hB hsm hnat <|
    (brownianChaosTotal_iff_dense_orderedChainSpan hB hsm).2 hdense
end Malliavin.BrownianIteratedConstruction
