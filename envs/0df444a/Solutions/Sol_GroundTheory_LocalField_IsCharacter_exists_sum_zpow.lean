-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.exists_sum_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:05.415803+00:00
-- url     : https://prove2.me/submissions/e606b542-4d27-4e40-b26a-b834950e615a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_monoidHom
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_nat
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) :
    ∃ (m : (Subgroup.zpowers s → ℂ) → ℕ) (β : (Subgroup.zpowers s → ℂ) → ℂ),
      (∀ ψ, β ψ ^ orderOf s = 1) ∧
        ∀ a : ℤ, χ (s ^ a) = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ ^ a := by
  classical
  set C := Subgroup.zpowers s
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hl : ∀ ψ ∈ irrChars C, ∃ l : C →* ℂˣ, ∀ c, ψ c = l c := fun ψ hψ ↦
    (mem_irrChars.mp hψ).exists_monoidHom
  choose! l hl using hl
  let s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  refine ⟨m, fun ψ ↦ if ψ ∈ irrChars C then (l ψ s' : ℂ) else 1, fun ψ ↦ ?_, fun a ↦ ?_⟩
  · dsimp only
    split_ifs
    · rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have : s' ^ orderOf s = 1 := by
        ext
        simp [s', pow_orderOf_eq_one]
      rw [this, map_one, Units.val_one]
    · exact one_pow _
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_zpow, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
    dsimp only
    rw [if_pos hψ, hl ψ hψ, map_zpow, Units.val_zpow_eq_zpow_val]
end IsCharacter
end GroundTheory.LocalField
