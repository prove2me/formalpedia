-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.hurwitzZeta_half_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:01.362808+00:00
-- url     : https://prove2.me/submissions/f491c386-7c17-4b88-b3eb-d39a9930bae5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution : hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
  have hne : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff 1).1 h
    rw [zsmul_eq_mul, mul_one] at hm
    have h1 : (0 : ℝ) < m := by rw [hm]; norm_num
    have h2 : (m : ℝ) < 1 := by rw [hm]; norm_num
    have h1' : 0 < m := by exact_mod_cast h1
    have h2' : m < 1 := by exact_mod_cast h2
    omega
  have hneg : -((1 / 2 : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_neg, show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, AddCircle.coe_sub,
      AddCircle.coe_period 1, sub_zero]
  have hodd : hurwitzZetaOdd ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
    have h := hurwitzZetaOdd_neg ((1 / 2 : ℝ) : UnitAddCircle) 0
    rw [hneg] at h
    have h2 : (2 : ℂ) * hurwitzZetaOdd ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hurwitzZeta, hurwitzZetaEven_apply_zero, if_neg hne, hodd, add_zero]
end GroundTheory.Global.Quadratic
