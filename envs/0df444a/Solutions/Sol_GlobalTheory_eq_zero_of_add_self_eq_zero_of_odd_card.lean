-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_add_self_eq_zero_of_odd_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:42.578989+00:00
-- url     : https://prove2.me/submissions/c8603f10-e317-4752-8bc2-3ccf22ebce70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

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
theorem _root_.solution (hodd : Odd (Fintype.card A)) {x : A}
    (hx : x + x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hodd
  have h := card_nsmul_eq_zero (x := x)
  rwa [hk, add_nsmul, mul_comm, mul_nsmul', two_nsmul, hx, nsmul_zero, zero_add, one_nsmul] at h
end GlobalTheory
