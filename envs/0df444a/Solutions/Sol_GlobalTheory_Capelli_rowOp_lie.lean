-- Prove2me | solution 1 for GlobalTheory.Capelli.rowOp_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:27.319376+00:00
-- url     : https://prove2.me/submissions/4116944b-2f8e-42ab-9eb4-50a03677c463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_colOp_lie

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
theorem _root_.solution [Fintype J] [DecidableEq I] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : I) :
    rowOp K z i j * rowOp K z k l - rowOp K z k l * rowOp K z i j =
      (if j = k then rowOp K z i l else 0) - (if l = i then rowOp K z k j else 0) :=
  colOp_lie (fun w : J × I => z w.swap) (hz.comp Prod.swap_injective) i j k l
end GlobalTheory.Capelli
