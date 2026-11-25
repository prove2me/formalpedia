-- Prove2me | solution 1 for GroundTheory.ProfCoh.not_dvd_superIndex_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:54.273847+00:00
-- url     : https://prove2.me/submissions/b8c8857e-a245-45f5-bf6f-b1f857544e24

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_index_sup_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_dvd_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_prime_dvd_iSup_iff


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
open Topology
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (p : Nat.Primes) (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ (p : ℕ) ∣ (H ⊔ (U : Subgroup G)).index := by
  rw [superIndex, Supernatural.ofNat_prime_dvd_iSup_iff, not_exists]
  refine forall_congr' fun U => ?_
  rw [Supernatural.ofNat_dvd_ofNat p.prop.ne_zero (index_sup_ne_zero H U)]
end GroundTheory.ProfCoh
