-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.IsBrownian.not_range_one_le_closure_span_unitIncrementLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:21.355214+00:00
-- url     : https://prove2.me/submissions/6d486fcd-552d-4801-9d3a-f639df853fa4

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegralKernel_boxKernel
import Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_integral_one_eq
import Theorems.Thm_Malliavin_brownianLp_half_notMem_closure_span_unitIncrementLp
import Theorems.Thm_Malliavin_brownianLp_zero

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
    ¬ LinearMap.range (J.integral 1).toLinearMap ≤
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by
  intro hle
  apply brownianLp_half_notMem_closure_span_unitIncrementLp hB
  have h1 : J.integral 1 (boxKernel (fun _ : Fin 1 ↦ 0) (fun _ ↦ 1 / 2)) =
      brownianLp hB (1 / 2) := by
    rw [hJ.integral_one_eq hB, wienerIntegralKernel_boxKernel hB (by norm_num), brownianLp_zero,
      sub_zero]
  rw [← h1]
  exact hle ⟨_, rfl⟩
end IteratedIntegralFamily.IsBrownian
end Malliavin
