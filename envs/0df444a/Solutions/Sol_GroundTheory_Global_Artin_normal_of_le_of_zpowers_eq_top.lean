-- Prove2me | solution 1 for GroundTheory.Global.Artin.normal_of_le_of_zpowers_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:26.357701+00:00
-- url     : https://prove2.me/submissions/d8f8bfd7-fdc4-4927-b6a7-90f89d0bd4dc

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
theorem _root_.solution (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) : K.Normal := ⟨fun n hn a ↦ by
  have h1 : a * n * a⁻¹ * n⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N) (n : Γ ⧸ N)]
    group
  have := K.mul_mem (hNK h1) hn
  simpa using this⟩
end GroundTheory.Global.Artin
