-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:10.351665+00:00
-- url     : https://prove2.me/submissions/325bc29d-342a-4b81-a23e-777d0d1c4d5e

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralRange_isOrtho

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
    {m n : ℕ} (hmn : m ≠ n) :
    (brownianHomogeneousChaos hB m : Submodule ℝ (RandomL2 P)) ⟂
      (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) := by
  change (brownianMultipleIntegralRange hB m).topologicalClosure ≤
    (brownianMultipleIntegralRange hB n).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact Submodule.topologicalClosure_minimal (brownianMultipleIntegralRange hB m)
    (brownianMultipleIntegralRange_isOrtho hB hsm hmn).le
    (brownianMultipleIntegralRange hB n).isClosed_orthogonal
end Malliavin.BrownianIteratedConstruction
