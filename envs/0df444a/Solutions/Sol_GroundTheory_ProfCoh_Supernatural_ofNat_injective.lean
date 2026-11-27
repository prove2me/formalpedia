-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.ofNat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:49.271536+00:00
-- url     : https://prove2.me/submissions/a91540bc-45fd-4b86-9b67-edbd8530e1f3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_dvd_ofNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m = ofNat n ↔ m = n := by
  refine ⟨fun h => Nat.dvd_antisymm ?_ ?_, fun h => h ▸ rfl⟩
  · exact (ofNat_dvd_ofNat hm hn).mp (h ▸ dvd_rfl)
  · exact (ofNat_dvd_ofNat hn hm).mp (h ▸ dvd_rfl)
end GroundTheory.ProfCoh.Supernatural
