-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup_iff_toFinite_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:22.049158+00:00
-- url     : https://prove2.me/submissions/562a4409-2e36-4d57-8060-a058dae24578

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_unitsLevel_zero


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
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by
  rw [mem_standardOpenSubgroup, mem_finiteLevel]
  refine forall_congr' fun v ↦ ?_
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
  rfl
end GroundTheory.Global.IdeleGroup
