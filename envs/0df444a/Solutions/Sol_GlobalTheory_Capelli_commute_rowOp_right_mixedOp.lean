-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_rowOp_right_mixedOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:31.610011+00:00
-- url     : https://prove2.me/submissions/6a75b5fa-962e-4a76-907b-067f6329e98b

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
    (y : I' × J → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w) (a b : I') (k l : J) :
    Commute (rowOp K y a b) (mixedOp K z y k l) :=
  Commute.sub_right (commute_rowOp_colOp y z (fun u w => (hzy w u).symm) _ _ _ _)
    (commute_rowOp_colOp_self y hy _ _ _ _)
end GlobalTheory.Capelli
