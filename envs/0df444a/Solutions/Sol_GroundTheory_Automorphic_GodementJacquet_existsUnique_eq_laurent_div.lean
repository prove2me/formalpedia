-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.existsUnique_eq_laurent_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:43.912648+00:00
-- url     : https://prove2.me/submissions/d58a5ff5-cab2-4208-b2ec-9eddfb35b433

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_mem_laurentSubalgebra
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_inv_mem_laurentSubalgebra
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_C_mem_laurentSubalgebra
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_laurentSubalgebra_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_pow_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_algebraMap_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_laurent_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_eq_of_laurent_div_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (I : Submodule ℂ (RatFunc ℂ))
    (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I)
    (h1 : (1 : RatFunc ℂ) ∈ I)
    (hD : ∃ D : ℂ[X], D ≠ 0 ∧ ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) :
    ∃! P : ℂ[X], P.eval 0 = 1 ∧
      ∀ R : RatFunc ℂ, R ∈ I ↔
        ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P := by
  classical
  obtain ⟨D, hD0, hDI⟩ := hD
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := RatFunc.algebraMap_ne_zero hD0

  let J : Ideal ℂ[X] :=
    { carrier := {Q | algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, add_div] at ha hb ⊢
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, zero_div]
        exact I.zero_mem
      smul_mem' := fun c {Q} hQ => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_div_assoc] at hQ ⊢
        exact algebraMap_mul_mem hX c hQ }
  have hJ : ∀ Q, Q ∈ J ↔
      algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I := fun Q => Iff.rfl
  set G := Submodule.IsPrincipal.generator J with hGdef
  have hGJ : G ∈ J := Submodule.IsPrincipal.generator_mem J
  have hdvd : ∀ Q, Q ∈ J ↔ G ∣ Q := fun Q => Submodule.IsPrincipal.mem_iff_generator_dvd J
  have hDJ : D ∈ J := by
    rw [hJ, div_self hφD]
    exact h1
  have hG0 : G ≠ 0 := by
    intro h
    have := (hdvd D).1 hDJ
    rw [h, zero_dvd_iff] at this
    exact hD0 this
  have hφG : algebraMap ℂ[X] (RatFunc ℂ) G ≠ 0 := RatFunc.algebraMap_ne_zero hG0
  have hGX : ¬ Polynomial.X ∣ G := by
    rintro ⟨G', hG'⟩
    have hG'0 : G' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hG'
      exact hG0 hG'
    have hG'J : G' ∈ J := by
      rw [hJ]
      have : algebraMap ℂ[X] (RatFunc ℂ) G' / algebraMap ℂ[X] (RatFunc ℂ) D =
          RatFunc.X⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D) := by
        rw [hG', map_mul, RatFunc.algebraMap_X]
        field_simp
      rw [this]
      exact hXinv _ hGJ
    have hle := Polynomial.natDegree_le_of_dvd ((hdvd G').1 hG'J) hG'0
    rw [hG', Polynomial.natDegree_mul Polynomial.X_ne_zero hG'0, Polynomial.natDegree_X] at hle
    omega

  have hchar : ∀ R, R ∈ I ↔ ∃ L ∈ laurentSubalgebra,
      R = algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D * L := by
    intro R
    constructor
    · intro hR
      obtain ⟨P, k, hPk⟩ := mem_laurentSubalgebra_iff.1 (hDI R hR)
      have hPJ : P ∈ J := by
        rw [hJ]
        have : algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) D =
            RatFunc.X ^ k * R := by
          rw [eq_div_iff (pow_ne_zero _ hXne)] at hPk
          rw [div_eq_iff hφD, ← hPk]
          ring
        rw [this]
        exact X_pow_mul_mem hX k hR
      obtain ⟨H, rfl⟩ := (hdvd P).1 hPJ
      refine ⟨algebraMap ℂ[X] (RatFunc ℂ) H / RatFunc.X ^ k,
        mem_laurentSubalgebra_iff.2 ⟨H, k, rfl⟩, ?_⟩
      rw [map_mul, eq_div_iff (pow_ne_zero _ hXne)] at hPk
      field_simp
      linear_combination hPk
    · rintro ⟨L, hL, rfl⟩
      rw [mul_comm]
      exact laurent_mul_mem hX hXinv hL hGJ

  obtain ⟨L1, hL1, h1eq⟩ := (hchar 1).1 h1
  obtain ⟨H, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL1
  have hDXk : D * Polynomial.X ^ k = G * H := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h1eq
    linear_combination h1eq
  have hGD : G ∣ D := by
    have hcop : IsCoprime G (Polynomial.X ^ k) :=
      Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hGX
    exact hcop.dvd_of_dvd_mul_right ⟨H, hDXk⟩
  obtain ⟨E, hE⟩ := hGD
  have hE0 : E ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hE
    exact hD0 hE
  obtain ⟨E₁, hE₁, hE₁X⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd E hE0 0
  simp only [map_zero, sub_zero] at hE₁ hE₁X
  set j := E.rootMultiplicity 0
  have hc : E₁.eval 0 ≠ 0 := by
    intro h
    apply hE₁X
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  set c := E₁.eval 0 with hcdef
  have hE₁0 : E₁ ≠ 0 := by
    rintro rfl
    exact hE₁X (dvd_zero _)
  have hφE₁ : algebraMap ℂ[X] (RatFunc ℂ) E₁ ≠ 0 := RatFunc.algebraMap_ne_zero hE₁0
  have hCc : RatFunc.C c ≠ 0 := by
    rw [← RatFunc.algebraMap_eq_C]
    exact (_root_.map_ne_zero _).2 hc
  have hGD' : algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D =
      (RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) E₁)⁻¹ := by
    rw [hE, hE₁, map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  have hφP : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) =
      (RatFunc.C c)⁻¹ * algebraMap ℂ[X] (RatFunc ℂ) E₁ := by
    rw [map_mul, RatFunc.algebraMap_C, map_inv₀]
  have hexists : (Polynomial.C c⁻¹ * E₁).eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ I ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) := by
    refine ⟨by rw [Polynomial.eval_mul, Polynomial.eval_C, ← hcdef, inv_mul_cancel₀ hc], ?_⟩
    intro R
    rw [hchar R, hφP, hGD']
    constructor
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * (RatFunc.X ^ j)⁻¹ * (RatFunc.C c)⁻¹,
        mul_mem (mul_mem hL (by rw [← inv_pow]; exact pow_mem X_inv_mem_laurentSubalgebra j))
          (by rw [← map_inv₀]; exact C_mem_laurentSubalgebra _), ?_⟩
      field_simp
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * RatFunc.X ^ j * RatFunc.C c,
        mul_mem (mul_mem hL (pow_mem X_mem_laurentSubalgebra j)) (C_mem_laurentSubalgebra c), ?_⟩
      field_simp
  refine ⟨Polynomial.C c⁻¹ * E₁, hexists, ?_⟩
  rintro P' ⟨hP'0, hP'⟩
  exact (eq_of_laurent_div_iff hexists.1 hP'0 fun R => (hexists.2 R).symm.trans (hP' R)).symm
end GroundTheory.Automorphic.GodementJacquet
