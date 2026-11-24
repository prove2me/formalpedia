-- Prove2me | solution 1 for GlobalTheory.HenselianNorm.exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:17:16.813495+00:00
-- url     : https://prove2.me/submissions/8b656ca2-7ee0-4f5b-841a-d2d000529ca9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselian
import Theorems.Thm_GlobalTheory_HenselianNorm_exists_norm_eq_one_add
import Theorems.Thm_GlobalTheory_T_finite_involution_fixed_unit_eq_mul_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.HenselianNorm
namespace GlobalTheory.HenselianNorm
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I]
    [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) →
    (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro R _ I _ _ c hc hI hω u hcu hu
  obtain ⟨ω, D, hD⟩ := hω
  have hcD : (c ω - ω) * c ↑D⁻¹ = 1 := by
    have h := congrArg c D.mul_inv
    rw [map_mul, map_one, hD, map_sub, hc] at h
    exact h
  have hw : ω * ↑D⁻¹ + c (ω * ↑D⁻¹) = 1 := by
    have hinv : (↑D⁻¹ : R) * (ω - c ω) = 1 := by rw [← hD]; exact D.inv_mul
    rw [map_mul]
    linear_combination (1 - ω * ↑D⁻¹) * hcD - ω * c ↑D⁻¹ * hinv
  have hI' : I ≤ I.comap c := fun x hx => hI x hx
  let cb : R ⧸ I →+* R ⧸ I := Ideal.quotientMap I c hI'
  have hmk : ∀ x, cb (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c x) :=
    fun x => Ideal.quotientMap_mk
  have hcb : ∀ x, cb (cb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hmk, hmk, hc]
  have hunit : IsUnit (Ideal.Quotient.mk I ω - cb (Ideal.Quotient.mk I ω)) := by
    rw [hmk, ← map_sub, ← hD]
    exact D.isUnit.map _
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj (R ⧸ I) cb hcb ⟨_, hunit⟩ (Ideal.Quotient.mk I u)
    (by rw [hmk, hcu]) (hu.map _)
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective xb
  rw [hmk, ← map_mul] at hxb
  have hmem : x₀ * c x₀ - u ∈ I := Ideal.Quotient.eq.mp hxb
  obtain ⟨U, rfl⟩ := hu
  have hcU : c ↑U⁻¹ = ↑U⁻¹ := by
    have h : (U : R) * c ↑U⁻¹ = 1 := by
      rw [← hcu, ← map_mul, U.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  obtain ⟨a, ha⟩ : ∃ a, a = (x₀ * c x₀ - ↑U) * ↑U⁻¹ := ⟨_, rfl⟩
  have haI : a ∈ I := ha ▸ I.mul_mem_right _ hmem
  have hca : c a = a := by
    rw [ha]
    simp only [map_mul, map_sub, hc, hcu, hcU]
    ring
  obtain ⟨V, hV⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac haI)) 1
  have hcV : c ↑V = ↑V := by rw [hV, map_add, map_mul, map_one, hca]
  have hcVi : c ↑V⁻¹ = ↑V⁻¹ := by
    have h : (V : R) * c ↑V⁻¹ = 1 := by
      rw [← hcV, ← map_mul, V.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  have heI : (↑V⁻¹ : R) - 1 ∈ I := by
    have h : (↑V⁻¹ : R) - 1 = -(↑V⁻¹ * a) := by
      linear_combination (-(↑V⁻¹ : R)) * hV + V.inv_mul
    rw [h]
    exact I.neg_mem (I.mul_mem_left _ haI)
  obtain ⟨y, hy⟩ := exists_norm_eq_one_add I c hc hI hw heI (by rw [map_sub, hcVi, map_one])
  have hvU : x₀ * c x₀ = ↑U * ↑V := by
    rw [hV, ha]
    linear_combination (-(x₀ * c x₀ - ↑U)) * U.mul_inv
  refine ⟨x₀ * y, ?_⟩
  rw [map_mul]
  linear_combination (x₀ * c x₀) * hy + (↑V⁻¹ : R) * hvU + (↑U : R) * V.mul_inv
end GlobalTheory.HenselianNorm
