-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.congrData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:21.232625+00:00
-- url     : https://prove2.me/submissions/a142e12d-84c6-4d5c-83c9-c1f2dca480c2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_nat
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_monoidHom
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
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
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) (hζ : IsPrimitiveRoot ζ (Nat.card G))
    {b : ℤ} (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ N = 1) : CongrData ζ N s a χ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hval : ∀ ψ ∈ irrChars C, ∀ x : C, ψ x ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := fun ψ hψ x ↦
    (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin x hζ
      (by rw [← Subgroup.orderOf_coe]; exact orderOf_dvd_natCard _)
  have hsN : s' ^ N = (s' ^ a) ^ N := by
    apply Subtype.ext
    simp only [s', Subgroup.coe_pow, Subgroup.coe_zpow]
    have hc : Commute (s ^ a) (s ^ b) := (Commute.refl s).zpow_zpow a b
    rw [← hab, hc.mul_pow, hb, mul_one, hab]
  refine ⟨irrChars C, inferInstance, fun ψ ↦ (m ψ : Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    fun ψ ↦ ⟨ψ.1 s', hval ψ.1 ψ.2 s'⟩, fun ψ ↦ ⟨ψ.1 (s' ^ a), hval ψ.1 ψ.2 _⟩, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨l, hl⟩ := (mem_irrChars.mp ψ.2).exists_monoidHom
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [hl, hl, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, hsN]
  · have h := congrFun hm s'
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    change χ (s' : G) = _
    rw [h, ← Finset.sum_coe_sort]
    simp
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Subgroup.coe_zpow] at h
    change χ ((s' : G) ^ a) = _
    rw [h, ← Finset.sum_coe_sort]
    simp
end IsCharacter
end GroundTheory.LocalField
