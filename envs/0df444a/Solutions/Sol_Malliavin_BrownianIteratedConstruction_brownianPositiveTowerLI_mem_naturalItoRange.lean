-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_mem_naturalItoRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:54.381723+00:00
-- url     : https://prove2.me/submissions/89ce2d0a-2653-405f-8bc5-9d7a77d1badc

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_range_brownianPositiveTowerLI
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_naturalItoRange
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
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    brownianPositiveTowerLI hB hsm f ∈ naturalItoRange hB hsm hnat := by
  apply Submodule.topologicalClosure_minimal
    (⨆ n : ℕ,
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)))
  · exact iSup_le fun n =>
      brownianHomogeneousChaos_le_naturalItoRange hB hsm hnat (n + 1)
        (Nat.zero_lt_succ n)
  · exact isClosed_naturalItoRange hB hsm hnat
  · rw [← range_brownianPositiveTowerLI hB hsm]
    exact LinearMap.mem_range_self (brownianPositiveTowerLI hB hsm).toLinearMap f
end Malliavin.BrownianIteratedConstruction
