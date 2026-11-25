-- Prove2me | solution 1 for GroundTheory.Global.Artin.sum_conj_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:01.768028+00:00
-- url     : https://prove2.me/submissions/70593e2b-6a40-4ffe-aa1a-d2408dfe75ab

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_inv_mul_mul_mem_of_normal
import Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_conj_mem_of_le
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
theorem _root_.solution [Fintype I] (hID : I ≤ D) [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (F : G → ℂ) (m : ℤ) :
    ∑ i : I, F (t⁻¹ * (φ ^ m * i) * t) = ∑ i : I, F (φ ^ m * i) := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) := ⟨_, rfl⟩
  have hc : c ∈ I := hcdef ▸ zpow_inv_mul_conj_mem_of_le hφ hgen ht m
  let σ : I → I := fun i ↦ ⟨c * (t⁻¹ * i * t), I.mul_mem hc (inv_mul_mul_mem_of_normal hID ht i.2)⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    have h1 : c * (t⁻¹ * (i : G) * t) = c * (t⁻¹ * (j : G) * t) := congrArg Subtype.val hij
    apply Subtype.ext
    simpa using h1
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hσ) _ _ fun i ↦ ?_
  congr 1
  change t⁻¹ * (φ ^ m * i) * t = φ ^ m * (c * (t⁻¹ * i * t))
  rw [hcdef]
  group
end GroundTheory.Global.Artin
