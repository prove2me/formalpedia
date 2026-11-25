-- Prove2me | solution 1 for GroundTheory.Global.Modulus.congruenceSubgroup_le_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:12.453821+00:00
-- url     : https://prove2.me/submissions/38131af4-178b-4256-a2d1-c3e4f2f1d6d4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_finiteLevel_zero
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup_iff_toFinite_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution :
    𝔪.congruenceSubgroup ≤ standardOpenSubgroup K := fun x hx ↦ by
  rw [mem_standardOpenSubgroup_iff_toFinite_mem]
  exact finiteLevel_le_finiteLevel_zero _ (Subgroup.mem_inf.1 hx).1
end GroundTheory.Global.Modulus
