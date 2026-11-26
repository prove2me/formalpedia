-- Prove2me | solution 1 for Malliavin.wienerIntegralKernel_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:57.985912+00:00
-- url     : https://prove2.me/submissions/08c3da7b-56a8-4470-add8-55ed8e4f0cce

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc
import Theorems.Thm_Malliavin_wienerIntegralKernel_apply
import Theorems.Thm_Malliavin_kernelToLine_boxKernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    wienerIntegralKernel hB (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      brownianLp hB b - brownianLp hB a := by
  rw [wienerIntegralKernel_apply, kernelToLine_boxKernel,
    wienerIntegral_indicatorConstLp_Ioc hB hab]
end Malliavin
