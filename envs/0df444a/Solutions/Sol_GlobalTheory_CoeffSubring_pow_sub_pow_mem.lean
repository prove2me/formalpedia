-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.pow_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:10.951066+00:00
-- url     : https://prove2.me/submissions/94389880-c9fd-45a9-989c-7c2a453bc779

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution (h0 : (p : S) ∈ maximalIdeal S) {x y : S} (h : x - y ∈ maximalIdeal S)
    (n : ℕ) : x ^ p ^ n - y ^ p ^ n ∈ maximalIdeal S ^ (n + 1) :=
  SModEq.sub_mem.1 ((SModEq.sub_mem.2 h).pow_pow_add_one h0 n)
end GlobalTheory.CoeffSubring
