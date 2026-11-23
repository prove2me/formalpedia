-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_colOp_colOp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:50.081724+00:00
-- url     : https://prove2.me/submissions/24d5f15b-0599-4ec9-8ca6-a11e7c140406

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
theorem _root_.solution [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (i j : J) (k l : J') :
    Commute (colOp K z i j) (colOp K y k l) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    commute_polar (hzy _ _) (hzy _ _).symm
end GlobalTheory.Capelli
