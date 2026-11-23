-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_rowOp_colOp_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:22.726799+00:00
-- url     : https://prove2.me/submissions/e9747ba1-3e14-4136-9ad1-0cb31fbab2a4

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
theorem _root_.solution [Fintype I] [Fintype J] (z : I × J → σ)
    (hz : Function.Injective z) (a b : I) (k l : J) :
    Commute (rowOp K z a b) (colOp K z k l) := by
  classical
  have h : rowOp K z a b * colOp K z k l - colOp K z k l * rowOp K z a b =
      ∑ m, ∑ c, (polar K (z (a, m)) (z (b, m)) * polar K (z (c, k)) (z (c, l)) -
        polar K (z (c, k)) (z (c, l)) * polar K (z (a, m)) (z (b, m))) := by
    simp only [colOp, rowOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    exact congrArg₂ (· - ·) rfl Finset.sum_comm
  refine sub_eq_zero.mp ?_
  rw [h]
  simp [polar_lie, hz.eq_iff, ite_and]
end GlobalTheory.Capelli
