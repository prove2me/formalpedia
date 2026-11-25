-- Prove2me | solution 1 for GlobalTheory.hasUnitLeadingExpansion_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:56.016655+00:00
-- url     : https://prove2.me/submissions/bf9391cc-9910-4bd6-83d2-ef2738207ada

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_C_mem_integralSeries
import Theorems.Thm_GlobalTheory_X_mem_integralSeries
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_mul
import Theorems.Thm_GlobalTheory_qParam_one_eq_pow
import Theorems.Thm_GlobalTheory_exists_hasQExpansion_modularJ_comp
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_const
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_sub


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
theorem _root_.solution {n a d : ℕ} {b : ℤ} (hn : a * d = n) (hn0 : n ≠ 0)
    (hsq : ¬ IsSquare n) {w : ℍ → ℍ} (hw : ∀ τ, (w τ : ℂ) = (a * τ + b) / d) :
    HasUnitLeadingExpansion n fun τ ↦ modularJ τ - modularJ (w τ) := by
  have ha : a ≠ 0 := by rintro rfl; simp [← hn] at hn0
  have hd : d ≠ 0 := by rintro rfl; simp [← hn] at hn0
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  set ζ : ℂ := cexp (2 * π * Complex.I * b / d) with hζ
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I b]
    congr 1
    field_simp
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ1 : IsIntegral ℤ ζ := .of_pow (Nat.pos_of_ne_zero hd) (hζd ▸ isIntegral_one)
  have hζ2 : IsIntegral ℤ ζ⁻¹ := .of_pow (Nat.pos_of_ne_zero hd)
    (by rw [inv_pow, hζd, inv_one]; exact isIntegral_one)
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_hasQExpansion_modularJ_comp (n := n) (w := id)
    isIntegral_one hn0 (fun τ ↦ by rw [one_mul, id, qParam_one_eq_pow hn0])
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_hasQExpansion_modularJ_comp (n := n) (w := w)
    hζ1 (e := a * a) (mul_ne_zero ha ha) (fun τ ↦ by
      simp only [hw, hζ, Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add, ← hn]
      congr 1
      push_cast
      field_simp
      ring)
  have hq := HasQExpansion.qParam (n : ℝ)
  rcases lt_trichotomy (a * a) n with h | h | h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨n, φ - C ζ⁻¹ * X ^ (k + 1) * ψ, sub_mem hφ1 (mul_mem (mul_mem (C_mem_integralSeries hζ2)
      (pow_mem X_mem_integralSeries _)) hψ1), by simp [hφ2], by simpa [hφ2] using isIntegral_one,
      (hφ3.sub (((HasQExpansion.const _ ζ⁻¹).mul (hq.pow (k + 1))).mul hψ3)).congr fun τ ↦ ?_⟩
    generalize 𝕢 n τ = q
    rw [hk, id]
    field_simp
    ring
  · exact absurd ⟨a, h.symm⟩ hsq
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨a * a, X ^ (k + 1) * φ - C ζ⁻¹ * ψ, sub_mem (mul_mem
      (pow_mem X_mem_integralSeries _) hφ1) (mul_mem (C_mem_integralSeries hζ2) hψ1),
      by simp [hψ2, hζ0], by simpa [hψ2] using hζ1.neg,
      (((hq.pow (k + 1)).mul hφ3).sub ((HasQExpansion.const _ ζ⁻¹).mul hψ3)).congr fun τ ↦ ?_⟩
    generalize 𝕢 n τ = q
    rw [hk, id]
    field_simp
    ring
end GlobalTheory
