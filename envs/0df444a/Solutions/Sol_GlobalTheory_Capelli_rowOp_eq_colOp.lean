-- Prove2me | solution 1 for GlobalTheory.Capelli.rowOp_eq_colOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:38.513657+00:00
-- url     : https://prove2.me/submissions/f25c7864-a418-4b74-ac5d-6b39bea4afdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}
namespace GlobalTheory.Capelli
theorem _root_.solution [Fintype J] (z : I × J → σ) (a b : I) :
    rowOp K z a b = colOp K (fun w : J × I => z w.swap) a b := rfl
end GlobalTheory.Capelli
