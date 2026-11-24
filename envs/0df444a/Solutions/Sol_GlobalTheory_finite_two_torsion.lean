-- Prove2me | solution 1 for GlobalTheory.finite_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:04.672864+00:00
-- url     : https://prove2.me/submissions/60ad348f-64d6-4467-937d-57ec1991d241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_finite_points_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
variable [CharZero F] [DecidableEq F]
namespace GlobalTheory
theorem _root_.solution : {P : W.toAffine.Point | 2 • P = 0}.Finite := by
  refine finite_points_of_root (W.Ψ₂Sq_ne_zero (by norm_num)) fun x y h hP => ?_
  have hy : y = W.toAffine.negY x y := by
    by_contra hy
    rw [Set.mem_setOf_eq, two_nsmul, Point.add_self_of_Y_ne hy] at hP
    exact Point.some_ne_zero _ hP
  have hE := (equation_iff ..).mp h.1
  rw [negY] at hy
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination -4 * hE + (2 * y + W.a₁ * x + W.a₃) * hy
end GlobalTheory
