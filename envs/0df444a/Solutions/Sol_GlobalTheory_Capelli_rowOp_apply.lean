-- Prove2me | solution 1 for GlobalTheory.Capelli.rowOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:11.372685+00:00
-- url     : https://prove2.me/submissions/cc080488-cc3d-4664-971a-71917fdd12fa

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
theorem _root_.solution [Fintype J] (z : I × J → σ) (a b : I) (P : MvPolynomial σ K) :
    rowOp K z a b P = ∑ k, X (z (a, k)) * pderiv (z (b, k)) P := by
  simp [rowOp, LinearMap.sum_apply]
end GlobalTheory.Capelli
