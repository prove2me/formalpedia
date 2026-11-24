-- Prove2me | solution 1 for GlobalTheory.finite_quotient_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:11.892197+00:00
-- url     : https://prove2.me/submissions/bf592bb7-3c42-4673-8f23-24a6e9702cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_natCard_quotient_range_mulVecLin

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
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) :
    Finite ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quotient_range_mulVecLin hd]; simpa using hd)
end GlobalTheory
