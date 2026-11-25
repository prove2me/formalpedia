-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpow_inv_mul_conj_mem_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:35.973712+00:00
-- url     : https://prove2.me/submissions/8161682d-d4a5-434f-ae95-d4623db84894

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_conj_mem
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
theorem _root_.solution [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (m : ℤ) : (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) ∈ I := by
  have := zpow_inv_mul_conj_mem hgen ⟨t, ht⟩ m
  simpa using Subgroup.mem_subgroupOf.1 this
end GroundTheory.Global.Artin
