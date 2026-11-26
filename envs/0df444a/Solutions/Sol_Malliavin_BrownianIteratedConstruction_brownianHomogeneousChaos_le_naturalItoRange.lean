-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_naturalItoRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:09.580708+00:00
-- url     : https://prove2.me/submissions/c4313544-68d6-4d9a-929d-b1f078b3f4a8

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_mem_naturalItoRange
import Theorems.Thm_Malliavin_isClosed_naturalItoRange


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
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (hn : 0 < n) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      naturalItoRange hB hsm hnat := by
  unfold brownianHomogeneousChaos
  apply Submodule.topologicalClosure_minimal
  · rintro F ⟨f, rfl⟩
    cases n with
    | zero => exact (Nat.lt_irrefl 0 hn).elim
    | succ n => exact positiveIntegralCLM_mem_naturalItoRange hB hsm hnat n f
  · exact isClosed_naturalItoRange hB hsm hnat
end Malliavin.BrownianIteratedConstruction
