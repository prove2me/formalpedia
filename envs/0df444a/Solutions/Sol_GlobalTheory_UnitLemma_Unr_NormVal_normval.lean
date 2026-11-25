-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormVal.normval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:08.541048+00:00
-- url     : https://prove2.me/submissions/16a84f9a-1e7d-4c18-b8bf-9505b1c3d566

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_inv__f61eb60cc841
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_exists_lift_of_val_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_val_algebraMap_unit
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_exists_val_eq_one
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_norm_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
namespace GlobalTheory.UnitLemma.Unr.NormVal
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  intro K K' d φ hφ hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hfr : Module.finrank K.E K'.E = d := hφ.2.2.2.2
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (hfr ▸ hd)
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero]
    simp [val]
  obtain ⟨π, hπ⟩ := exists_val_eq_one K.O (E := K.E)
  have hπ0 : π ≠ 0 := by rintro rfl; simp [val] at hπ
  have hφπ : val K'.O (φ π) = 1 := by rw [hφ.2.2.1, hπ]
  have hφπ0 : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
  set n := val K'.O y with hn
  set a := (-n).toNat
  set b := n.toNat
  have hab : (b : ℤ) - a = n := Int.toNat_sub_toNat_neg n
  set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))
  have hvu : val K'.O u = 0 := by
    rw [hu, val_mul' _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)),
      val_mul' _ hy (pow_ne_zero _ hφπ0), val_inv' _ (pow_ne_zero _ hφπ0), val_pow' _ hφπ0, val_pow' _ hφπ0, hφπ, ← hn]
    omega
  have hvu' : val K'.O u⁻¹ = 0 := by rw [val_inv' _ hu0, hvu]; rfl
  obtain ⟨u₁, hu₁⟩ := exists_lift_of_val_eq_zero K'.O hu0 hvu
  obtain ⟨u₂, hu₂⟩ := exists_lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'
  obtain ⟨m₁, hm₁⟩ := norm_integral K K' d φ hφ hd u₁
  obtain ⟨m₂, hm₂⟩ := norm_integral K K' d φ hφ hd u₂
  have hunit : IsUnit m₁ := by
    have h12 : m₁ * m₂ = 1 := by
      apply IsFractionRing.injective K.O K.E
      rw [map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]
    exact IsUnit.of_mul_eq_one m₂ h12
  have hNu : val K.O (Algebra.norm K.E u) = 0 := by
    rw [← hu₁, ← hm₁]; exact val_algebraMap_unit K.O m₁ hunit
  have hNu0 : Algebra.norm K.E u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
  have hNy0 : Algebra.norm K.E y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hNφ : Algebra.norm K.E (φ π) = π ^ d := by
    rw [← hfr]; exact Algebra.norm_algebraMap π
  have key : y * φ π ^ a = u * φ π ^ b := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]
  have key2 := congrArg (fun x => val K.O (Algebra.norm K.E x)) key
  simp only [map_mul, map_pow, hNφ] at key2
  rw [val_mul' _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul' _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)),
    val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ hπ0, hNu, hπ] at key2
  rw [← hab]
  push_cast at key2 ⊢
  linarith
end GlobalTheory.UnitLemma.Unr.NormVal
