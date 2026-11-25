-- Prove2me | solution 1 for GroundTheory.FunctionField.valuation_eq_of_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:36.258136+00:00
-- url     : https://prove2.me/submissions/b0fddce2-6a18-42d5-8784-0082d6f42bd4

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
namespace GroundTheory.FunctionField
theorem _root_.solution {F : Type*} [Field F] {v₁ v₂ : Valuation F ℤᵐ⁰}
    (h : v₁.IsEquiv v₂) (h₁ : Function.Surjective v₁) (h₂ : Function.Surjective v₂) : v₁ = v₂ := by
  have disc : ∀ y : ℤᵐ⁰, y < 1 → y ≤ WithZero.exp (-1) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_le
    · rw [← WithZero.exp_log hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
      rw [← WithZero.exp_log hy0, WithZero.exp_le_exp]
      omega
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  obtain ⟨π, hπ⟩ := h₁ (WithZero.exp (-1))
  obtain ⟨π', hπ'⟩ := h₂ (WithZero.exp (-1))
  have hπ2 : v₂ π = WithZero.exp (-1) := by
    have h2lt : v₂ π < 1 := h.lt_one_iff_lt_one.1 (hπ ▸ hlt)
    have h1 : v₁ π' < 1 := h.lt_one_iff_lt_one.2 (hπ' ▸ hlt)
    have h3 : v₂ π' ≤ v₂ π := h.le_iff_le.1 (hπ ▸ disc _ h1)
    exact le_antisymm (disc _ h2lt) (hπ' ▸ h3)
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx1 : v₁ x = WithZero.exp (WithZero.log (v₁ x)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm
  have hy : v₁ (x * π ^ (WithZero.log (v₁ x))) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx1, WithZero.log_exp, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp
  have hy2 := h.eq_one_iff_eq_one.1 hy
  rw [map_mul, map_zpow₀, hπ2, ← WithZero.exp_zsmul] at hy2
  rw [hx1, eq_inv_of_mul_eq_one_left hy2, ← WithZero.exp_neg]
  congr 1
  simp
end GroundTheory.FunctionField
