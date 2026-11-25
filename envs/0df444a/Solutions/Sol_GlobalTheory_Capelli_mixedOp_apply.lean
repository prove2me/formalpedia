-- Prove2me | solution 1 for GlobalTheory.Capelli.mixedOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:27.493397+00:00
-- url     : https://prove2.me/submissions/f4030635-6c96-4cab-9f62-caf5f744f895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_colOp_apply
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
theorem _root_.solution [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J → σ) (k l : J)
    (P : MvPolynomial σ K) :
    mixedOp K z y k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P -
      ∑ b, X (y (b, l)) * pderiv (y (b, k)) P := by
  simp [mixedOp, colOp_apply]
end GlobalTheory.Capelli
