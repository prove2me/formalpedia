-- Prove2me | solution 1 for Malliavin.multipleIntegralCLM_mem_homogeneousChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:07.607332+00:00
-- url     : https://prove2.me/submissions/540b886a-7c20-47a5-a219-5e74a8f0fa82

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f ∈ homogeneousChaos hB n := by
  apply Submodule.le_topologicalClosure (multipleIntegralRange hB n)
  exact LinearMap.mem_range_self (multipleIntegralCLM hB n).toLinearMap f
end Malliavin
