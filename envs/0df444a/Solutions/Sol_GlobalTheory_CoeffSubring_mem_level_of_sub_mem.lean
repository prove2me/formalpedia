-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.mem_level_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:34.13863+00:00
-- url     : https://prove2.me/submissions/8e09501b-49c3-4306-b49f-57711d16fed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem_pow

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
theorem _root_.solution {n : ℕ} {x a : S} (ha : a ∈ level p L n)
    (hx : x - a ∈ maximalIdeal S ^ (n + 1)) : x ∈ level p L n := by
  simpa using add_mem (mem_level_of_mem_pow hx) ha
end GlobalTheory.CoeffSubring
