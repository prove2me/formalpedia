-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_wickChainCompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:59.21532+00:00
-- url     : https://prove2.me/submissions/ce94a6ac-e224-4d97-a6be-911abf5e1840

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_dense_orderedChainSpan_of_wickChainCompatible
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_dense_orderedChainSpan


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
    (hgen : IsWienerGenerated B) (hwick : BrownianWickChainCompatible hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  exact naturalMartingaleRepresentation_of_dense_orderedChainSpan hB hsm hnat
    (dense_orderedChainSpan_of_wickChainCompatible hB hgen hwick)
end Malliavin.BrownianIteratedConstruction
