-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpow_inv_mul_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:30.670983+00:00
-- url     : https://prove2.me/submissions/20d53133-d908-4292-96e1-7abe3710433c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_mul_comm_of_zpowers_eq_top
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
variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}
namespace GroundTheory.Global.Artin
theorem _root_.solution (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤) (a : Γ) (m : ℤ) :
    (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ N := by
  rw [← QuotientGroup.eq]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N)⁻¹, inv_mul_cancel_right]
end GroundTheory.Global.Artin
