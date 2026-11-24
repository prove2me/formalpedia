-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.level_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:38.284142+00:00
-- url     : https://prove2.me/submissions/013f2f8f-e784-40c7-a7cb-df99283b8bdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_pow_mem_level
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem
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
theorem _root_.solution : Antitone (level p L) := by
  refine antitone_nat_of_succ_le fun n => Subring.closure_le.2 ?_
  rintro _ ((⟨x, rfl⟩ | hx) | hx)
  · simpa only [pow_succ', pow_mul, SetLike.mem_coe] using pow_mem_level n (x ^ p)
  · exact mem_level_of_mem hx
  · exact mem_level_of_mem_pow (Ideal.pow_le_pow_right (by omega) hx)
end GlobalTheory.CoeffSubring
