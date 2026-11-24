-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:19.019115+00:00
-- url     : https://prove2.me/submissions/172de7f7-6735-44f7-a0be-ed25cad60f2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_integrand_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ C / (s.re - 1 / 2) := by
  have hlt : -(s.re + 1 / 2) < -1 := by linarith
  refine (norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) (norm_integrand_le hC s)).trans ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
  refine le_of_eq ?_
  have : -(s.re + 1 / 2) + 1 = -(s.re - 1 / 2) := by ring
  rw [this, neg_div_neg_eq, mul_one_div]
end GlobalTheory.Hk.RayCont
