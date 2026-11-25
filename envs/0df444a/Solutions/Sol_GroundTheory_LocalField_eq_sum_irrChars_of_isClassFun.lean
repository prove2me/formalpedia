-- Prove2me | solution 1 for GroundTheory.LocalField.eq_sum_irrChars_of_isClassFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:06:18.919117+00:00
-- url     : https://prove2.me/submissions/b0cfc7c4-9b90-4009-92a5-5c4dc9b45159

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_sum_irrChars_mul_apply
import Theorems.Thm_GroundTheory_LocalField_sum_mul_irr_apply

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
theorem _root_.solution {f : G → ℂ} (hf : IsClassFun f) :
    f = ∑ ψ ∈ irrChars G, charInner G f ψ • ψ := by
  classical
  funext h
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : f h = (Nat.card G : ℂ)⁻¹ * ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h) := by
    simp_rw [sum_irrChars_mul_apply, inv_mul_eq_one, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), mul_comm (f h), ← mul_assoc, inv_mul_cancel₀ hG,
      one_mul]
  have hswap : ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h) =
      ∑ ψ ∈ irrChars G, ∑ g, f g * (ψ 1 * ψ (g⁻¹ * h)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [key, Finset.sum_apply, hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
  have h1 := (mem_irrChars.mp hψ).one_ne_zero
  have := sum_mul_irr_apply hf (mem_irrChars.mp hψ) h
  calc (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (ψ 1 * ψ (g⁻¹ * h))
      = (Nat.card G : ℂ)⁻¹ * ψ 1 * ∑ g, f g * ψ (g⁻¹ * h) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ ↦ by ring
    _ = (charInner G f ψ • ψ) h := by
        rw [this, Pi.smul_apply, smul_eq_mul]
        field_simp
end GroundTheory.LocalField
