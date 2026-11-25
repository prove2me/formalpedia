-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpow_mem_iff_index_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:36.513797+00:00
-- url     : https://prove2.me/submissions/c7cbae0e-b04b-4788-b47a-7b14df10033d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_normal_of_le_of_zpowers_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}
namespace GroundTheory.Global.Artin
theorem _root_.solution [Finite Γ] (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) (m : ℤ) : g ^ m ∈ K ↔ (K.index : ℤ) ∣ m := by
  have := normal_of_le_of_zpowers_eq_top hgen hNK
  have hgenK : ∀ y : Γ ⧸ K, y ∈ Subgroup.zpowers (g : Γ ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with | H d => ?_
    have hd : (d : Γ ⧸ N) ∈ Subgroup.zpowers (g : Γ ⧸ N) := by rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hd
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hj
    exact hNK hj
  rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hgenK,
    orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
end GroundTheory.Global.Artin
