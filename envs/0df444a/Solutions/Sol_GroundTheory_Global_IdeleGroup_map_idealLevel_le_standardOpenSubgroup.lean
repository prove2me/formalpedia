-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.map_idealLevel_le_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:29.579903+00:00
-- url     : https://prove2.me/submissions/5fb1d817-c606-4821-a217-95e96d863915

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_finiteLevel_zero
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup_iff_toFinite_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (𝔪 : Ideal (𝓞 K)) :
    (idealLevel 𝔪).map ofFinite ≤ standardOpenSubgroup K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_standardOpenSubgroup_iff_toFinite_mem, toFinite_ofFinite]
  exact finiteLevel_le_finiteLevel_zero _ hx
end GroundTheory.Global.IdeleGroup
