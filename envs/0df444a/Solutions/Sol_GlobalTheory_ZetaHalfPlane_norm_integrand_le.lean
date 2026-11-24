-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.norm_integrand_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:21.048773+00:00
-- url     : https://prove2.me/submissions/a41c2f70-4249-4e1d-906b-98b9fa6aea2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_fract_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution (s : ℂ) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)
end GlobalTheory.ZetaHalfPlane
