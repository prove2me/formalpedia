-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianStepPowerLp_mem_orderedChainSpan_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:49.331148+00:00
-- url     : https://prove2.me/submissions/273ed38a-ba5c-4b7d-a773-06906a737b7c

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_brownianWickPowerLp_eq_power

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
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianStepPowerLp hB v n ∈
      (brownianOrderedChainSpan hB).topologicalClosure := by
  have hpower : brownianStepPowerLp hB v n ∈
      Submodule.span ℝ (Set.range (brownianStepPowerLp hB v)) :=
    Submodule.subset_span ⟨n, rfl⟩
  rw [← span_range_brownianWickPowerLp_eq_power hB v] at hpower
  exact (Submodule.span_le.mpr <| by
    rintro _ ⟨k, rfl⟩
    exact hwick v k) hpower
end Malliavin.BrownianIteratedConstruction
