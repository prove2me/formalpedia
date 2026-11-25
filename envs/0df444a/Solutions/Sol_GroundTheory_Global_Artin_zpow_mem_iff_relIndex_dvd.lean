-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpow_mem_iff_relIndex_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:02.51114+00:00
-- url     : https://prove2.me/submissions/6f1fa154-8dd8-4107-b13b-c88269d83ba8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_zpow_mem_iff_index_dvd
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable {H D I : Subgroup G}
namespace GroundTheory.Global.Artin
theorem _root_.solution [Finite G] [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {K : Subgroup G}
    (hIK : I ≤ K) (m : ℤ) : φ ^ m ∈ K ↔ (K.relIndex D : ℤ) ∣ m := by
  have h := zpow_mem_iff_index_dvd hgen (K := K.subgroupOf D)
    (fun y hy ↦ Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hy))) m
  rw [Subgroup.mem_subgroupOf] at h
  simpa [Subgroup.relIndex] using h
end GroundTheory.Global.Artin
