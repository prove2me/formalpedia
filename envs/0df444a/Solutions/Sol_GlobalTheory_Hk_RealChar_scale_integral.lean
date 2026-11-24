-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.scale_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:10.121804+00:00
-- url     : https://prove2.me/submissions/45a2dcfb-69a5-4374-8ffa-33e4cee642a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_scale_eq

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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution (y : ℝ) {n : ℝ} (hn : 0 < n) :
    ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = besW (y * n) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w hw => scale_eq y hn hw), integral_const_mul,
    integral_comp_mul_right_Ioi (kerW (y * n)) 0 hn, zero_mul, smul_eq_mul]
  unfold besW
  field_simp
end GlobalTheory.Hk.RealChar
