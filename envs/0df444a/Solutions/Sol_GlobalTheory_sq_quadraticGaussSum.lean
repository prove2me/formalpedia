-- Prove2me | solution 1 for GlobalTheory.sq_quadraticGaussSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:53.836799+00:00
-- url     : https://prove2.me/submissions/53414dfa-d70f-49c7-ad95-b290c9c5c633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_sq_sum_addChar_quadraticMap
import Theorems.Thm_GlobalTheory_ratCircleChar_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [AddCommGroup A] [Fintype A]
namespace GlobalTheory
theorem _root_.solution (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A (AddCircle (1 : ℚ)))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) :
    (∑ x, ratCircleChar (q x)) ^ 2 =
      (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) :=
  sq_sum_addChar_quadraticMap hodd q _ fun x hx =>
    hnd x fun y => ratCircleChar_eq_one_iff.1 (hx y)
end GlobalTheory
