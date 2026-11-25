-- Prove2me | solution 1 for GroundTheory.LocalField.sum_mul_irr_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:31.997999+00:00
-- url     : https://prove2.me/submissions/62db8d8b-0a23-4d8e-a2f5-0acb870c4d46

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_one_ne_zero

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
theorem _root_.solution {f : G → ℂ} (hf : IsClassFun f) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ)
    (h : G) :
    ∑ g, f g * ψ (g⁻¹ * h) = (Nat.card G : ℂ) * charInner G f ψ / ψ 1 * ψ h := by
  have h1 := hψ.one_ne_zero
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hψ
  let T : V →ₗ[ℂ] V := ∑ g, f g • ρ g⁻¹
  have hT : ∀ k, T ∘ₗ ρ k = ρ k ∘ₗ T := by
    intro k
    ext v
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul]
    refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ fun g ↦ ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    rw [show f (k⁻¹ * g * k) = f g by simpa using hf g k⁻¹, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, show k * (k⁻¹ * g * k)⁻¹ = g⁻¹ * k by group]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 ⟨T, hT⟩
  have hTc : T = c • LinearMap.id := by
    have := congrArg IntertwiningMap.toLinearMap hc
    rw [Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  have htr : ∀ h' : G, LinearMap.trace ℂ V (T ∘ₗ ρ h') = ∑ g, f g * ρ.character (g⁻¹ * h') := by
    intro h'
    have hcomp : T ∘ₗ ρ h' = ∑ g, f g • ρ (g⁻¹ * h') := by
      ext v
      simp [T, LinearMap.sum_apply, map_mul]
    rw [hcomp, map_sum]
    simp only [map_smul, smul_eq_mul, Representation.character]
  have hval : ∀ h' : G, ∑ g, f g * ρ.character (g⁻¹ * h') = c * ρ.character h' := by
    intro h'
    rw [← htr, hTc, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]
    rfl
  have hc' : c = (Nat.card G : ℂ) * charInner G f ρ.character / ρ.character 1 := by
    have h0 := hval 1
    simp only [mul_one] at h0
    have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [charInner_apply, ← mul_assoc, mul_inv_cancel₀ hG, one_mul, h0]
    field_simp
  rw [hval, hc']
end GroundTheory.LocalField
