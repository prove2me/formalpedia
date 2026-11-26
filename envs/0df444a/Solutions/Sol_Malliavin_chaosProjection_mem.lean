-- Prove2me | solution 1 for Malliavin.chaosProjection_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:06.973977+00:00
-- url     : https://prove2.me/submissions/7f105edd-5408-418d-93e0-4871dfe951bc

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ) (F : RandomL2 P) :
    chaosProjection hB n F ∈ homogeneousChaos hB n :=
  Submodule.starProjection_apply_mem _ _
end Malliavin
