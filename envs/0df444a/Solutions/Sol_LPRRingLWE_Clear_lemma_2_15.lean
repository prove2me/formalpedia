-- Prove2me | solution 1 for LPRRingLWE.Clear.lemma_2_15
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:50:36.291991+00:00
-- url     : https://prove2.me/submissions/3b174099-120f-4d82-821d-4cabe018e1f2

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

open LPRRingLWE.Clear in
open NumberField in
open scoped nonZeroDivisors in
theorem solution {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I)
    (hcop : ClearedCoprime t I J) (M : FractionalIdeal (𝓞 K)⁰ K) (hM : M ≠ 0) :
    Function.Surjective (theta t I J ht M) ∧
      LinearMap.ker (theta t I J ht M) = sub M ((J : FractionalIdeal (𝓞 K)⁰ K) * M) := by
  have hII : (I : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ = 1 :=
    mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have hc := hcop.2
  unfold cleared at hc
  set T := FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K t) with hT
  set I' := (I : FractionalIdeal (𝓞 K)⁰ K) with hI'
  set J' := (J : FractionalIdeal (𝓞 K)⁰ K) with hJ'
  have key1 : I' * M = T * M + I' * J' * M := by
    calc I' * M = I' * M * (T * I'⁻¹ + J') := by rw [hc, mul_one]
      _ = T * M * (I' * I'⁻¹) + I' * J' * M := by ring
      _ = T * M + I' * J' * M := by rw [hII, mul_one]
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨xv, hx⟩ := x
    have hx' : xv ∈ I' * M := hx
    rw [key1, FractionalIdeal.mem_add] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    obtain ⟨u, hu, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp ha
    refine ⟨⟨u, hu⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    show ((_ : K) - _) ∈ (I' * J' * M : FractionalIdeal (𝓞 K)⁰ K)
    subst hab
    show algebraMap (𝓞 K) K t * u - (algebraMap (𝓞 K) K t * u + b) ∈ (I' * J' * M : FractionalIdeal (𝓞 K)⁰ K)
    have : algebraMap (𝓞 K) K t * u - (algebraMap (𝓞 K) K t * u + b) = -b := by ring
    rw [this]
    exact Submodule.neg_mem ((I' * J' * M : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) hb
  · ext u
    show Submodule.Quotient.mk _ = 0 ↔ (u : K) ∈ (J' * M : FractionalIdeal (𝓞 K)⁰ K)
    rw [Submodule.Quotient.mk_eq_zero]
    show algebraMap (𝓞 K) K t * (u : K) ∈ (I' * J' * M : FractionalIdeal (𝓞 K)⁰ K) ↔ _
    constructor
    · intro h
      rw [← FractionalIdeal.spanSingleton_le_iff_mem]
      have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K t * u) * I'⁻¹
            + FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K) * J' := by
        rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← hT]
        calc _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K) * (T * I'⁻¹ + J') := by
                rw [hc, mul_one]
          _ = _ := by ring
      rw [hs]
      rw [← FractionalIdeal.sup_eq_add]
      refine sup_le (?_) (?_)
      · calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K t * u) * I'⁻¹
            ≤ I' * J' * M * I'⁻¹ :=
              mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr h) _
          _ = J' * M * (I' * I'⁻¹) := by ring
          _ = J' * M := by rw [hII, mul_one]
      · rw [mul_comm]
        exact mul_le_mul_right (FractionalIdeal.spanSingleton_le_iff_mem.mpr u.2) _
    · intro h
      have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ht) h
      rwa [← mul_assoc] at this

#print axioms solution
