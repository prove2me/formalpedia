-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPolynomialSpan_le_orderedChainSpan_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:30.582711+00:00
-- url     : https://prove2.me/submissions/322be9ce-8b62-4e51-9339-6951470e9f07

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepPowerLp_mem_orderedChainSpan_closure

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB) :
    brownianPolynomialSpan hB ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨v, n⟩, rfl⟩
  exact brownianStepPowerLp_mem_orderedChainSpan_closure hB hwick v n
end Malliavin.BrownianIteratedConstruction
