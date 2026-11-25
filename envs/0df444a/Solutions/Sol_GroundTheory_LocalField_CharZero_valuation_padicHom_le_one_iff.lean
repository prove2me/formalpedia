-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.valuation_padicHom_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:50.776903+00:00
-- url     : https://prove2.me/submissions/f6a12fb0-6d0d-4889-9f83-319e44f3bbde

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_padicInt_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]
namespace GroundTheory.LocalField.CharZero
theorem _root_.solution (x : ℚ_[p]) :
    valuation K (padicHom K p x) ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hv => ?_, fun hx => valuation_padicHom_padicInt_le_one K p ⟨x, hx⟩⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  set y : ℚ_[p] := ((p : ℚ_[p]) * x)⁻¹
  have hxinv : ‖x⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have : ‖x⁻¹‖ < (p : ℝ) ^ (0 : ℤ) := by
      rw [norm_inv, zpow_zero]
      exact inv_lt_one_of_one_lt₀ (not_le.mp hx)
    simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x⁻¹ 0).mp this
  have hy : ‖y‖ ≤ 1 := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.Prime.pos Fact.out)
    simp only [y, mul_inv, norm_mul, norm_inv, Padic.norm_p, inv_inv] at hxinv ⊢
    rw [zpow_neg_one] at hxinv
    calc (p : ℝ) * ‖x‖⁻¹ ≤ p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hvy := valuation_padicHom_padicInt_le_one K p ⟨y, hy⟩
  simp only at hvy
  have hone : padicHom K p x * padicHom K p y * padicHom K p p = 1 := by
    rw [← map_mul, ← map_mul]
    simp [y, hx0, hp0]
  have hvp : valuation K (padicHom K p p) < 1 := by
    simpa using valuation_p_lt_one K p
  have := congrArg (valuation K) hone
  rw [map_mul, map_mul, map_one] at this
  have h1 : valuation K (padicHom K p x) * valuation K (padicHom K p y) ≤ 1 :=
    mul_le_one' hv hvy
  have h2 := (mul_le_of_le_one_left' h1 : _ ≤ valuation K (padicHom K p p))
  exact absurd (this ▸ h2) (not_le.mpr hvp)
end GroundTheory.LocalField.CharZero
