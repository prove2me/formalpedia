-- Prove2me | solution 1 for GlobalTheory.Capelli.polar_lie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:23.684056+00:00
-- url     : https://prove2.me/submissions/b80c6210-019e-4b6b-92c4-dcfbb741baa2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_pderiv_swap
import Theorems.Thm_P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
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
namespace GlobalTheory.Capelli
theorem _root_.solution [DecidableEq σ] (u v w s : σ) :
    polar K u v * polar K w s - polar K w s * polar K u v =
      (if v = w then polar K u s else 0) - (if s = u then polar K w v else 0) := by
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, polar_apply, pderiv_X_mul',
    pderiv_swap v s]
  split_ifs <;> simp <;> ring
end GlobalTheory.Capelli
