-- Prove2me | solution 1 for GlobalTheory.Capelli.commute_mixedOp_mixedOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:19.138152+00:00
-- url     : https://prove2.me/submissions/d1ffc592-a6ec-466e-b425-3fd04a62357e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_commute_colOp_colOp

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
theorem _root_.solution {I₁ I₂ I₃ I₄ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    [Fintype I₄] (z : I₁ × J → σ) (y : I₂ × J → σ) (z' : I₃ × J' → σ) (y' : I₄ × J' → σ)
    (hzz : ∀ u w, z u ≠ z' w) (hzy : ∀ u w, z u ≠ y' w) (hyz : ∀ u w, y u ≠ z' w)
    (hyy : ∀ u w, y u ≠ y' w) (i j : J) (k l : J') :
    Commute (mixedOp K z y i j) (mixedOp K z' y' k l) :=
  Commute.sub_left
    (Commute.sub_right (commute_colOp_colOp z z' hzz _ _ _ _) (commute_colOp_colOp z y' hzy _ _ _ _))
    (Commute.sub_right (commute_colOp_colOp y z' hyz _ _ _ _) (commute_colOp_colOp y y' hyy _ _ _ _))
end GlobalTheory.Capelli
