-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.IsBrownian.not_top_le_closure_sup_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:54.957925+00:00
-- url     : https://prove2.me/submissions/32be76e3-fc4a-44ce-b033-f0af9c9ba19c

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_integral_one_eq
import Theorems.Thm_Malliavin_range_wienerIntegral
import Theorems.Thm_Malliavin_exists_ne_zero_orthogonal_firstChaos
import Theorems.Thm_Malliavin_IteratedIntegralFamily_inner_integral_zero_eq_zero

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
namespace IteratedIntegralFamily.IsBrownian
theorem _root_.solution
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    ¬ (⊤ : Submodule ℝ (RandomL2 P)) ≤
      (LinearMap.range (J.integral 0).toLinearMap ⊔
        LinearMap.range (J.integral 1).toLinearMap).topologicalClosure := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  intro hle
  obtain ⟨Y, hY0, hYc, hY1⟩ := exists_ne_zero_orthogonal_firstChaos hB
  have horth : Y ∈ (LinearMap.range (J.integral 0).toLinearMap ⊔
      LinearMap.range (J.integral 1).toLinearMap).topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro u hu
    rw [Submodule.mem_sup] at hu
    obtain ⟨a, ⟨f, rfl⟩, b, ⟨g, rfl⟩, rfl⟩ := hu
    rw [inner_add_right, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      J.inner_integral_zero_eq_zero hYc f, hJ.integral_one_eq hB, zero_add]
    apply hY1
    rw [← range_wienerIntegral]
    exact ⟨kernelToLine g, rfl⟩
  rw [Submodule.mem_orthogonal] at horth
  exact hY0 (inner_self_eq_zero.mp (horth Y (hle Submodule.mem_top)))
end IteratedIntegralFamily.IsBrownian
end Malliavin
