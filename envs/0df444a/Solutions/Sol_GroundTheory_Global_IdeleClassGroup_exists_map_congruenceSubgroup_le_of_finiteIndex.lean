-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.exists_map_congruenceSubgroup_le_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:22.168711+00:00
-- url     : https://prove2.me/submissions/b04c63b6-7451-48e2-a4d1-2b19068a9d72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_exists_map_congruenceSubgroup_le

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
theorem _root_.solution
    (H : Subgroup (IdeleClassGroup K)) (hH : IsOpen (H : Set (IdeleClassGroup K)))
    (_ : H.FiniteIndex) :
    ∃ 𝔪 : Modulus K, 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H :=
  (IdeleClassGroup.exists_map_congruenceSubgroup_le H hH).imp fun _ h ↦ h.2
end IdeleClassGroup
end GroundTheory.Global
