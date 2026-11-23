-- Prove2me | solution 1 for GlobalTheory.Capelli.colOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:15.262177+00:00
-- url     : https://prove2.me/submissions/35e18f0e-fae3-4fb4-a553-575d6b8fad44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
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
variable {I J I' J' : Type*}
namespace GlobalTheory.Capelli
theorem _root_.solution [Fintype I] (z : I × J → σ) (k l : J) (P : MvPolynomial σ K) :
    colOp K z k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P := by
  simp [colOp, LinearMap.sum_apply]
end GlobalTheory.Capelli
