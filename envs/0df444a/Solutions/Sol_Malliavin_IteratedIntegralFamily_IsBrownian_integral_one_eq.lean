-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.IsBrownian.integral_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:01.519398+00:00
-- url     : https://prove2.me/submissions/fb7e2380-4a0d-4180-9336-cd42a51e4c90

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegralKernel_box
import Theorems.Thm_Malliavin_dense_span_boxKernel_one

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
namespace IteratedIntegralFamily.IsBrownian
theorem _root_.solution {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    J.integral 1 = wienerIntegralKernel hB := by
  refine ContinuousLinearMap.ext_on dense_span_boxKernel_one ?_
  rintro _ ⟨t, rfl⟩
  have h1 := hJ.box 1 (fun _ ↦ 0) (fun _ ↦ t) (fun _ ↦ zero_le) (fun i j hij ↦
    (hij.ne (Subsingleton.elim i j)).elim)
  have h2 := wienerIntegralKernel_box hB (fun _ : Fin 1 ↦ 0) (fun _ ↦ t) (fun _ ↦ zero_le)
  exact Lp.ext (h1.trans h2.symm)
end IteratedIntegralFamily.IsBrownian
end Malliavin
