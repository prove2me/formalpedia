-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_iff_higher
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:29.454516+00:00
-- url     : https://prove2.me/submissions/1a0f7829-6601-4f7e-8a4e-c6d25ea6833c

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_zero
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_one
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_stepToRandom_mem_orderedChainSpan

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
theorem _root_.solution (hB : IsPreBrownianReal B P) :
    BrownianWickChainCompatible hB ↔ BrownianHigherWickChainCompatible hB := by
  constructor
  · intro hwick v n _hn
    exact hwick v n
  · intro hhigher v n
    cases n with
    | zero =>
        rw [brownianWickPowerLp_zero hB v]
        apply Submodule.le_topologicalClosure
        let a : OrderedBoxIndex 0 :=
          { u := fun i ↦ Fin.elim0 i
            v := fun i ↦ Fin.elim0 i
            valid := fun i ↦ Fin.elim0 i
            ordered := fun i ↦ Fin.elim0 i }
        rw [← chainIntegralLp_zero hB a.u a.v]
        exact Submodule.subset_span ⟨⟨0, a⟩, rfl⟩
    | succ n =>
        cases n with
        | zero =>
            rw [brownianWickPowerLp_one hB v]
            exact Submodule.le_topologicalClosure _
              (stepToRandom_mem_orderedChainSpan hB v)
        | succ n =>
            exact hhigher v (n + 2) (by omega)
end Malliavin.BrownianIteratedConstruction
