-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_wickChainCompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:04.041488+00:00
-- url     : https://prove2.me/submissions/6d06547f-e05a-481c-818d-879342f38cff

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPolynomialSpan_le_orderedChainSpan_closure
import Theorems.Thm_Malliavin_dense_brownianPolynomialSpan


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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    (hwick : BrownianWickChainCompatible hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  have hpoly := dense_brownianPolynomialSpan hB hgen
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at hpoly
  rw [← hpoly]
  exact Submodule.topologicalClosure_minimal (brownianPolynomialSpan hB)
    (brownianPolynomialSpan_le_orderedChainSpan_closure hB hwick)
    (brownianOrderedChainSpan hB).isClosed_topologicalClosure
end Malliavin.BrownianIteratedConstruction
