-- Prove2me | solution 1 for GlobalTheory.HasUnitLeadingExpansion.isIntegral_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:48.168733+00:00
-- url     : https://prove2.me/submissions/e928f360-3a8d-41c7-8790-6d99f26a8272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_mul
import Theorems.Thm_GlobalTheory_qParam_one_eq_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_isBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_of_hasSum_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_unique
import Theorems.Thm_GlobalTheory_exists_polynomial_modularJ_of_hasQExpansion
import Theorems.Thm_GlobalTheory_hasQExpansion_qParam_pow_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
namespace HasUnitLeadingExpansion
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {f : ℍ → ℂ}
    (hf : HasUnitLeadingExpansion n f) (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    {τ₀ : ℍ} (h0 : f τ₀ = 0) : IsIntegral ℤ (modularJ τ₀) := by
  obtain ⟨e, ψ, h1, h2, h3, h4⟩ := hf
  have hn' : (0 : ℝ) < n := by positivity
  have hq (τ : ℍ) : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  have h5 : HasQExpansion n (fun τ ↦ 𝕢 1 τ ^ e * f τ ^ n) (ψ ^ n) :=
    (h4.pow n).congr fun τ ↦ by rw [qParam_one_eq_pow hn]; ring
  have hhol : MDiff fun τ ↦ f τ ^ n := by
    have := (h5.mdifferentiable hn').div
      (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow e) (fun τ ↦ pow_ne_zero _ (hq τ))
    convert! this using 1
    ext τ
    simp only [Pi.div_apply, Pi.pow_apply]
    field_simp [hq τ]
  have hinv' (γ : SL(2, ℤ)) (τ : ℍ) : f (γ • τ) ^ n = f τ ^ n := by rw [hinv]
  have h6 := hasQExpansion_qParam_pow_mul (f := fun τ ↦ f τ ^ n) hinv' hhol
    (h5.isBoundedAtImInfty hn')
  set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ e * f τ ^ n
  have h7 := (HasQExpansion.of_hasSum_pow (h := n) (c := fun m ↦ coeff m φ) hn
    (fun τ ↦ by rw [← qParam_one_eq_pow hn]; exact h6 τ)).unique hn' h5
  have h8 (k : ℕ) : coeff k φ = coeff (n * k) (ψ ^ n) := by
    simp [← h7, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  obtain ⟨P, hP1, hP2, hP3, hP4⟩ := exists_polynomial_modularJ_of_hasQExpansion
    (integralClosure ℤ ℂ).toSubring.toAddSubgroup (f := fun τ ↦ f τ ^ n) hinv' h6
    (fun k ↦ h8 k ▸ pow_mem h1 n _)
  set u := constantCoeff ψ ^ n with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ h2
  have hu1 : IsIntegral ℤ u⁻¹ := by rw [hu, ← inv_pow]; exact h3.pow n
  have hP5 : P.coeff e = u := by simp [hP2, h8, hu]
  have hP6 : P.leadingCoeff = u := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hP1 (hP5 ▸ hu0), hP5]
  have hmonic : (Polynomial.C u⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hP6, inv_mul_cancel₀ hu0])
  have heval : (Polynomial.C u⁻¹ * P).eval (modularJ τ₀) = 0 := by
    simp [← hP4, h0, hn]
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic (fun h ↦ ?_)
    (heval ▸ isIntegral_zero) fun i ↦ ?_
  · rw [hmonic.natDegree_eq_zero.mp h] at heval
    simp at heval
  · rw [Polynomial.coeff_C_mul]
    exact hu1.mul (hP3 i)
end HasUnitLeadingExpansion
end GlobalTheory
