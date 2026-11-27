-- Prove2me | solution 1 for GroundTheory.Global.Modulus.isOpen_map_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:02:44.188465+00:00
-- url     : https://prove2.me/submissions/2c92aebb-7075-4041-9f79-93418be64df1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_isOpenMap_mk
import Theorems.Thm_GroundTheory_Global_Modulus_isOpen_congruenceSubgroup


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
namespace Modulus
theorem _root_.solution (𝔪 : Modulus K) :
    IsOpen (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) : Set (IdeleClassGroup K)) := by
  rw [Subgroup.coe_map]
  exact IdeleClassGroup.isOpenMap_mk K _ 𝔪.isOpen_congruenceSubgroup
end Modulus
end GroundTheory.Global
