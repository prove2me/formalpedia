-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_rowOp_rowOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:38.038882+00:00
-- url     : https://prove2.me/submissions/191421f3-c536-4215-8198-87abe5cdd7f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_commute_polar

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
theorem _root_.solution [Fintype J] [Fintype J'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (a b : I) (c d : I') :
    Commute (rowOp K z a b) (rowOp K y c d) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    commute_polar (hzy _ _) (hzy _ _).symm
end GlobalTheory.Capelli
