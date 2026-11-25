-- Prove2me | solution 1 for GlobalTheory.exists_integral_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:35.196104+00:00
-- url     : https://prove2.me/submissions/048f245e-2b60-44fc-a171-13869135f74b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Theorems.Thm_GlobalTheory_exists_integral_model_of_forms
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_deuringCurve
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_splitCurve
import Theorems.Thm_GlobalTheory_HasRationalTorsion_of_dvd
import Theorems.Thm_GlobalTheory_HasRationalTorsion_variableChange
import Theorems.Thm_P2M_GlobalTheory_HasRationalTorsion_exists_pow_twelve_eq___43dcc7f916ee


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]
variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
namespace GlobalTheory
theorem _root_.solution (hj : W.j ∈ (algebraMap A K).range)
    (h : HasRationalTorsion W L 12) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  obtain ⟨δ, hδ⟩ := h.exists_pow_twelve_eq_Δ
  have hΔ := W.isUnit_Δ.ne_zero
  have hδ0 : δ ≠ 0 := by rintro rfl; simp [← hδ] at hΔ
  set C₁ : VariableChange K := ⟨Units.mk0 δ hδ0, 0, 0, 0⟩ with hC₁
  have h' := h.variableChange C₁
  obtain ⟨C₂, P, Q, hu₂, e₂⟩ := (h'.of_dvd (by norm_num : 2 ∣ 12)).exists_splitCurve
  obtain ⟨C₃, a, b, -, hu₃, e₃, -⟩ := (h'.of_dvd (by norm_num : 3 ∣ 12)).exists_deuringCurve
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model_of_forms A (W := C₁ • W)
    (by rwa [variableChange_j]) (by rw [variableChange_Δ, ← hδ]; simp [hC₁, hδ0]) hu₂ hu₃ e₂ e₃
  exact ⟨C * C₁, W₀, by rw [mul_smul, e], h₀⟩
end GlobalTheory
