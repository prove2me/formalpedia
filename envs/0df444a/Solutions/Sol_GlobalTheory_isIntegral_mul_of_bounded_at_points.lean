-- Prove2me | solution 1 for GlobalTheory.isIntegral_mul_of_bounded_at_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:57.322751+00:00
-- url     : https://prove2.me/submissions/1ba69899-b5b5-4192-8b58-674942655630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegralCoeffZeroMulOfAevalInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
open Polynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint
end _root_.GlobalTheory
end GlobalTheory
