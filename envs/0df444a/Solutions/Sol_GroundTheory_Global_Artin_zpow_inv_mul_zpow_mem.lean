-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpow_inv_mul_zpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:48.974819+00:00
-- url     : https://prove2.me/submissions/27021bbc-0946-486a-aea2-fe10dc4ff6be

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
theorem _root_.solution [(I.subgroupOf D).Normal] {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a⁻¹ * b ∈ I) (k : ℤ) : (a ^ k)⁻¹ * b ^ k ∈ I := by
  have h : ((⟨a, ha⟩ : D) : D ⧸ I.subgroupOf D) = ((⟨b, hb⟩ : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  have h2 : (((⟨a, ha⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) =
      (((⟨b, hb⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, h]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  simpa using h2
end GroundTheory.Global.Artin
