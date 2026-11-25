-- Prove2me | solution 1 for GroundTheory.Global.Artin.inv_mul_mul_mem_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:22.939927+00:00
-- url     : https://prove2.me/submissions/a32fbaf1-1d19-4d67-9fd2-34ffc40193a8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
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
theorem _root_.solution (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] {t i : G}
    (ht : t ∈ D) (hi : i ∈ I) : t⁻¹ * i * t ∈ I := by
  have := hN.conj_mem ⟨i, hID hi⟩ (Subgroup.mem_subgroupOf.2 hi) (⟨t, ht⟩⁻¹)
  simpa using Subgroup.mem_subgroupOf.1 this
end GroundTheory.Global.Artin
