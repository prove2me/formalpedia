-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.range_brownianPositiveTowerLI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:36.085437+00:00
-- url     : https://prove2.me/submissions/c4b1ef54-3b8e-4ae6-9c52-dfe84daf3ab8

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI

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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    LinearMap.range (brownianPositiveTowerLI hB hsm).toLinearMap =
      (⨆ n : ℕ,
        (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P))
      ).topologicalClosure := by
  rw [brownianPositiveTowerLI,
    (brownianSimplexIntegralLI_orthogonalFamily hB hsm).range_linearIsometry]
  congr 1
  exact iSup_congr fun n =>
    (brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm n).symm
end Malliavin.BrownianIteratedConstruction
