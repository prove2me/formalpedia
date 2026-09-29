-- Prove2me | solution 1 for IsPrimitiveRoot.exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c6c521c5-ea62-5a51-81b3-f2a4530dd138

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

open Polynomial

theorem solution
    (q : ℕ) [Fact q.Prime]
    (Z₀ : Type) [CommRing Z₀]
    (C : Type) [CommRing C] [Algebra Z₀ C] (w : C) (hw : Polynomial.aeval w (Polynomial.cyclotomic q Z₀) = 0)
    (A : Type) [CommRing A] [IsDomain A] [Algebra Z₀ A] (ζ : A) (hζ : IsPrimitiveRoot ζ q) :
    (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) = 0) ∧
    (∀ 𝔭 : Ideal (TensorProduct Z₀ A C), 𝔭.IsPrime →
      ∃ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ μ' : A),
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
      ((μ' ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
        ((μ - μ') ⊗ₜ[Z₀] (1 : C) : (TensorProduct Z₀ A C)) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ : A), 𝔭 ∈ minimalPrimes (TensorProduct Z₀ A C) →
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
        𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))})) ∈
          minimalPrimes ((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}) ∧
        Nonempty (((TensorProduct Z₀ A C) ⧸ 𝔭) ≃+*
          (((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}) ⧸
            𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}))))) := by
  classical
  have hq0 : 0 < q := (Fact.out : q.Prime).pos

  set ψ : A →+* (TensorProduct Z₀ A C) := Algebra.TensorProduct.includeLeftRingHom with hψ
  set φ : C →+* (TensorProduct Z₀ A C) := (Algebra.TensorProduct.includeRight (R := Z₀) (A := A) (B := C)).toRingHom with hφ
  have hψμ : ∀ μ : A, ψ μ = μ ⊗ₜ[Z₀] (1 : C) := fun μ => rfl
  have hφw : φ w = (1 : A) ⊗ₜ[Z₀] w := rfl

  have hi : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))) = 0 := by

    have h1 : Polynomial.cyclotomic q (TensorProduct Z₀ A C) = ∏ μ ∈ primitiveRoots q A, (Polynomial.X - Polynomial.C (ψ μ)) := by
      rw [← Polynomial.map_cyclotomic q ψ, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have h2 : Polynomial.eval (φ w) (Polynomial.cyclotomic q (TensorProduct Z₀ A C)) = 0 := by
      rw [← Polynomial.map_cyclotomic q φ, Polynomial.eval_map, ← Polynomial.map_cyclotomic q (algebraMap Z₀ C)]
      rw [Polynomial.eval₂_map]
      have : Polynomial.eval₂ (φ.comp (algebraMap Z₀ C)) (φ w) (Polynomial.cyclotomic q Z₀) = φ (Polynomial.eval₂ (algebraMap Z₀ C) w (Polynomial.cyclotomic q Z₀)) := by
        rw [Polynomial.hom_eval₂]
      rw [this]
      have hw' : Polynomial.eval₂ (algebraMap Z₀ C) w (Polynomial.cyclotomic q Z₀) = 0 := by
        rw [← Polynomial.aeval_def]; exact hw
      rw [hw', map_zero]
    rw [h1, Polynomial.eval_prod] at h2
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2

    have h3 : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))) =
        ∏ μ ∈ primitiveRoots q A, (-(φ w - ψ μ)) := by
      apply Finset.prod_congr rfl; intro μ _; rw [hψμ, hφw, neg_sub]
    rw [h3, Finset.prod_neg, h2, mul_zero]
  refine ⟨hi, ?_, ?_, ?_⟩
  ·
    intro 𝔭 h𝔭
    haveI := h𝔭
    have : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))) ∈ 𝔭 := by rw [hi]; exact zero_mem _
    exact Ideal.IsPrime.prod_mem_iff.mp this
  ·
    intro 𝔭 μ μ' h h'
    have := 𝔭.sub_mem h h'
    rwa [sub_sub_sub_cancel_right, ← TensorProduct.sub_tmul] at this
  ·
    intro 𝔭 μ h𝔭 hj
    generalize hJ : (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))} : Ideal (TensorProduct Z₀ A C)) = J
    have hJle : J ≤ 𝔭 := by rw [← hJ, Ideal.span_le]; rintro _ rfl; exact hj
    have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
    haveI h𝔭p : 𝔭.IsPrime := h𝔭.1.1
    have hcomap : Ideal.comap (Ideal.Quotient.mk J) (𝔭.map (Ideal.Quotient.mk J)) = 𝔭 := by
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJle]
    have hP'prime : (𝔭.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hJle)
    refine ⟨⟨⟨hP'prime, bot_le⟩, ?_⟩, ⟨?_⟩⟩
    ·
      intro r hr hrle
      have h1 : Ideal.comap (Ideal.Quotient.mk J) r ≤ 𝔭 := by
        rw [← hcomap]; exact Ideal.comap_mono hrle
      haveI : r.IsPrime := hr.1
      have h2 : 𝔭 ≤ Ideal.comap (Ideal.Quotient.mk J) r := h𝔭.2 ⟨Ideal.comap_isPrime _ r, bot_le⟩ h1
      calc 𝔭.map (Ideal.Quotient.mk J) ≤ (Ideal.comap (Ideal.Quotient.mk J) r).map (Ideal.Quotient.mk J) := Ideal.map_mono h2
        _ = r := Ideal.map_comap_of_surjective _ hsurj r
    ·
      have hsup : J ⊔ 𝔭 = 𝔭 := sup_eq_right.mpr hJle
      exact (Ideal.quotEquivOfEq hsup.symm).trans (DoubleQuot.quotQuotEquivQuotSup J 𝔭).symm

end S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero
end P2MW
export P2MW.S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero (solution)
