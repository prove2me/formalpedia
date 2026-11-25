-- Prove2me | solution 1 for GroundTheory.Global.exists_scale_of_weberValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:50.523705+00:00
-- url     : https://prove2.me/submissions/83f0a996-48e9-4fbd-968a-edf25cb15995

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_automorphismEquivRootsOfUnity_apply
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberValue_of_ne_zero
import Theorems.Thm_P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero
attribute [local simp] GroundTheory.Global.weberFunction_some
attribute [local simp] GroundTheory.Global.weberFunction_zero


attribute [local simp] GroundTheory.Global.automorphismEquivRootsOfUnity_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]
namespace GroundTheory.Global
theorem _root_.solution [IsAlgClosed F] (hW : IsShortForm W) {x₁ x₂ : F}
    (hx : weberValue W x₁ = weberValue W x₂) :
    ∃ v : F, v ≠ 0 ∧ v ^ 4 * W.a₄ = W.a₄ ∧ v ^ 6 * W.a₆ = W.a₆ ∧ v ^ 2 * x₁ = x₂ := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    rw [weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6] at hx
    have hc : g₂ W ^ 2 / W.Δ ≠ 0 := by simp [g₂, h4, hΔ]
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hc hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : F)
      have hi4 : i ^ 4 = 1 := by linear_combination (1 - i * i) * hi
      refine ⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩
      · rintro rfl
        simp at hi
      · linear_combination (-x₁) * hi - h
  by_cases h4 : W.a₄ = 0
  · rw [weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6] at hx
    have hc : g₃ W / W.Δ ≠ 0 := by simp [g₃, h6, hΔ]
    have hcube : x₁ ^ 3 = x₂ ^ 3 := mul_left_cancel₀ hc hx
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ = 0 := by
        rw [hx1, zero_pow (by norm_num)] at hcube
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm
      exact ⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩
    · obtain ⟨w, hw⟩ : ∃ w, w = x₂ / x₁ := ⟨_, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        rw [hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw3
      refine ⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩
      · rw [show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]
      · rw [show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]
  · rw [weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6] at hx
    have hc : g₂ W * g₃ W / W.Δ ≠ 0 := by simp [g₂, g₃, h4, h6, hΔ]
    have h : x₁ = x₂ := mul_left_cancel₀ hc hx
    exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
end GroundTheory.Global
