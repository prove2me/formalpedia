-- Prove2me | solution 1 for NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/449d1d8b-35ff-502b-8747-373daceb6f2d

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Circle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.NumberField IsDedekindDomain AutomorphicForm Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing AdelicBox.existsUnique_algebraMap_add_mem_adelicBox AdelicBox.exists_isCompact_adelicBox_subset"
namespace AdelicFourier
p2m_open "NumberField"

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

theorem exists_norm_apply_le_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℝ, ∀ x : 𝔸, ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨k, hk⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x).exists
  have hkx : ψ (ι k + x) = ψ x := by
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant k, one_mul]
  rw [← hkx]
  exact hM _ (hsub hk)

theorem norm_apply_le_one_of_bounded {ψ : AddChar 𝔸 ℂ} {M : ℝ} (hM : ∀ x : 𝔸, ‖ψ x‖ ≤ M)
    (x : 𝔸) : ‖ψ x‖ ≤ 1 := by
  by_contra h
  have h1 : 1 < ‖ψ x‖ := lt_of_not_ge h
  have hpow : ∀ n : ℕ, ‖ψ x‖ ^ n ≤ M := fun n => by
    rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
    exact hM _
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop M)).exists
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_apply_eq_one_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ‖ψ x‖ = 1 := by
  obtain ⟨M, hM⟩ := exists_norm_apply_le_of_isGlobalAddChar F hψ
  refine le_antisymm (norm_apply_le_one_of_bounded F hM x) ?_
  have hneg : ‖ψ (-x)‖ ≤ 1 := norm_apply_le_one_of_bounded F hM (-x)
  have hprod : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, norm_one]
  calc (1 : ℝ) = ‖ψ (-x)‖ * ‖ψ x‖ := hprod.symm
    _ ≤ 1 * ‖ψ x‖ := mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
    _ = ‖ψ x‖ := one_mul _

def toCircleAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) : AddChar 𝔸 Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x)⟩
  map_zero_eq_one' := by
    ext
    simp only [AddChar.map_zero_eq_one]
    rfl
  map_add_eq_mul' a b := by
    ext
    simp only [AddChar.map_add_eq_mul]
    rfl

theorem coe_toCircleAddChar_apply {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ((toCircleAddChar F hψ x : Circle) : ℂ) = ψ x := rfl

theorem exists_compAddChar_eq_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  ⟨toCircleAddChar F hψ, by ext x; rfl⟩

#print axioms norm_apply_eq_one_of_isGlobalAddChar_impl
#print axioms exists_compAddChar_eq_of_isGlobalAddChar_impl

example : ∀ {ψ : AddChar 𝔸 ℂ} (_ : IsGlobalAddChar F ψ) (x : 𝔸), ‖ψ x‖ = 1 :=
  fun hψ x => norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x
example : ∀ {ψ : AddChar 𝔸 ℂ} (_ : IsGlobalAddChar F ψ),
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  fun hψ => exists_compAddChar_eq_of_isGlobalAddChar_impl F hψ

end NumberField.AdelicFourier

end

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.NumberField AutomorphicForm"

theorem solution (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 := by
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x

end S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
end P2MW
export P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar (solution)
