-- Prove2me | solution 1 for GlobalTheory.Capelli.colOp_lie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:22.729266+00:00
-- url     : https://prove2.me/submissions/1e63f503-a948-409e-9e14-0ea2fa6704b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_polar_lie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}
namespace GlobalTheory.Capelli
theorem _root_.solution [Fintype I] [DecidableEq J] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : J) :
    colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j =
      (if j = k then colOp K z i l else 0) - (if l = i then colOp K z k j else 0) := by
  classical
  have h : colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j =
      ∑ a, ∑ b, (polar K (z (a, i)) (z (a, j)) * polar K (z (b, k)) (z (b, l)) -
        polar K (z (b, k)) (z (b, l)) * polar K (z (a, i)) (z (a, j))) := by
    simp only [colOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    exact congrArg₂ (· - ·) rfl Finset.sum_comm
  rw [h]
  simp only [polar_lie, hz.eq_iff, Prod.mk.injEq, Finset.sum_sub_distrib]
  refine congrArg₂ (· - ·) ?_ ?_
  · by_cases hjk : j = k <;> simp [hjk, colOp]
  · by_cases hli : l = i <;> simp [hli, colOp]
end GlobalTheory.Capelli
