-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.exists_map_congruenceSubgroup_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:33.727142+00:00
-- url     : https://prove2.me/submissions/acb8de52-c90b-4bf1-8690-eea396beb4f7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_exists_congruenceSubgroup_le
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
namespace GroundTheory.Global
namespace IdeleClassGroup
theorem _root_.solution (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Modulus.exists_congruenceSubgroup_le (H.comap (IdeleClassGroup.mk K))
    (hH.preimage (IdeleClassGroup.continuous_mk K))
  exact ⟨𝔪, h𝔪, Subgroup.map_le_iff_le_comap.2 hle⟩
end IdeleClassGroup
end GroundTheory.Global
