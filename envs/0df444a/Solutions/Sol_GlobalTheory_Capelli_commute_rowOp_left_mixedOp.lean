-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_rowOp_left_mixedOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:25.402557+00:00
-- url     : https://prove2.me/submissions/e6dee3cb-70d8-41d4-ab94-2deb3cc2fb4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_commute_rowOp_colOp
import Theorems.Thm_GlobalTheory_Capelli_commute_rowOp_colOp_self

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
theorem _root_.solution [Fintype I] [Fintype I'] [Fintype J] (z : I × J → σ)
    (hz : Function.Injective z) (y : I' × J → σ) (hzy : ∀ u w, z u ≠ y w) (a b : I) (k l : J) :
    Commute (rowOp K z a b) (mixedOp K z y k l) :=
  Commute.sub_right (commute_rowOp_colOp_self z hz _ _ _ _) (commute_rowOp_colOp z y hzy _ _ _ _)
end GlobalTheory.Capelli
