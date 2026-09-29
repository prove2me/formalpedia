-- Prove2me | solution 1 for NumberField.exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/384b1d1d-72fc-54d2-86d1-0465bc53bbd4

import Mathlib
import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

namespace SignedRaySol

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [CommGroup M]

abbrev pI (α : 𝓞 K) : FractionalIdeal ((𝓞 K)⁰) K :=
  ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)

theorem pI_ne_zero {α : 𝓞 K} (hα : α ≠ 0) : pI α ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
  exact hα

omit [NumberField K] in
theorem pI_mul (α β : 𝓞 K) : pI (α * β) = pI α * pI β := by
  rw [pI, pI, pI, ← FractionalIdeal.coeIdeal_mul, Ideal.span_singleton_mul_span_singleton]

theorem raySymbol_pI_mul (ψ : HeightOneSpectrum (𝓞 K) → M) {α β : 𝓞 K} (hα : α ≠ 0)
    (hβ : β ≠ 0) : raySymbol K ψ (pI (α * β)) = raySymbol K ψ (pI α) * raySymbol K ψ (pI β) := by
  rw [pI_mul]
  exact raySymbol_mul K ψ (pI_ne_zero hα) (pI_ne_zero hβ)

omit [NumberField K] in
theorem mul_sub_one_mem {I : Ideal (𝓞 K)} {a b : 𝓞 K} (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) :
    a * b - 1 ∈ I := by
  have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [this]
  exact I.add_mem (I.mul_mem_right _ ha) hb

omit [NumberField K] in

theorem realEmb_ne_zero (φ : K →+* ℝ) {α : 𝓞 K} (hα : α ≠ 0) : φ (algebraMap (𝓞 K) K α) ≠ 0 := by
  rw [map_ne_zero]
  exact RingOfIntegers.coe_ne_zero_iff.mpr hα

theorem prod_ne_zero_and_sub_one_mem_and_raySymbol (ψ : HeightOneSpectrum (𝓞 K) → M)
    (I : Ideal (𝓞 K)) {ι : Type*} (s : Finset ι) (f : ι → 𝓞 K) (h0 : ∀ i ∈ s, f i ≠ 0)
    (h1 : ∀ i ∈ s, f i - 1 ∈ I) :
    (∏ i ∈ s, f i) ≠ 0 ∧ (∏ i ∈ s, f i) - 1 ∈ I ∧
      raySymbol K ψ (pI (∏ i ∈ s, f i)) = ∏ i ∈ s, raySymbol K ψ (pI (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, by simp, ?_⟩
    rw [Finset.prod_empty, Finset.prod_empty, pI, Ideal.span_singleton_one, FractionalIdeal.coeIdeal_top]
    unfold raySymbol
    simp [FractionalIdeal.count_one]
  | insert a s ha ih =>
    obtain ⟨h0', h1', hr⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have ha0 : f a ≠ 0 := h0 a (Finset.mem_insert_self a s)
    have ha1 : f a - 1 ∈ I := h1 a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨mul_ne_zero ha0 h0', mul_sub_one_mem ha1 h1', by rw [raySymbol_pI_mul ψ ha0 h0', hr]⟩

section Main

theorem exists_alpha (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (φ₀ : K →+* ℝ) : ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
    ∀ φ : K →+* ℝ, φ (algebraMap (𝓞 K) K α) < 0 ↔ φ = φ₀ := by
  obtain ⟨α, h0, h1, h⟩ :=
    NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff K 𝔣 h𝔣 ({φ₀} : Set (K →+* ℝ))
  exact ⟨α, h0, h1, fun φ => by rw [h φ, Set.mem_singleton_iff]⟩

noncomputable def alpha (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (φ₀ : K →+* ℝ) : 𝓞 K := (exists_alpha 𝔣 h𝔣 φ₀).choose

variable (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)

theorem alpha_ne_zero (φ₀ : K →+* ℝ) : alpha 𝔣 h𝔣 φ₀ ≠ 0 := (exists_alpha 𝔣 h𝔣 φ₀).choose_spec.1

theorem alpha_sub_one_mem (φ₀ : K →+* ℝ) : alpha 𝔣 h𝔣 φ₀ - 1 ∈ 𝔣 :=
  (exists_alpha 𝔣 h𝔣 φ₀).choose_spec.2.1

theorem alpha_lt_zero_iff (φ₀ φ : K →+* ℝ) :
    φ (algebraMap (𝓞 K) K (alpha 𝔣 h𝔣 φ₀)) < 0 ↔ φ = φ₀ :=
  (exists_alpha 𝔣 h𝔣 φ₀).choose_spec.2.2 φ

theorem alpha_pos_of_ne {φ₀ φ : K →+* ℝ} (h : φ ≠ φ₀) :
    0 < φ (algebraMap (𝓞 K) K (alpha 𝔣 h𝔣 φ₀)) :=
  lt_of_le_of_ne (not_lt.mp (fun hlt => h ((alpha_lt_zero_iff 𝔣 h𝔣 φ₀ φ).mp hlt)))
    (realEmb_ne_zero φ (alpha_ne_zero 𝔣 h𝔣 φ₀)).symm

theorem prod_alpha_lt_zero_iff (ψ : HeightOneSpectrum (𝓞 K) → M) (s : Finset (K →+* ℝ))
    (φ : K →+* ℝ) :
    φ (algebraMap (𝓞 K) K (∏ φ₀ ∈ s, alpha 𝔣 h𝔣 φ₀)) < 0 ↔ φ ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, map_mul, map_mul, Finset.mem_insert]
    have hne : φ (algebraMap (𝓞 K) K (∏ φ₀ ∈ s, alpha 𝔣 h𝔣 φ₀)) ≠ 0 :=
      realEmb_ne_zero φ (prod_ne_zero_and_sub_one_mem_and_raySymbol ψ 𝔣 s _
        (fun i _ => alpha_ne_zero 𝔣 h𝔣 i) (fun i _ => alpha_sub_one_mem 𝔣 h𝔣 i)).1
    by_cases hφ : φ = a
    · have hneg : φ (algebraMap (𝓞 K) K (alpha 𝔣 h𝔣 a)) < 0 := (alpha_lt_zero_iff 𝔣 h𝔣 a φ).mpr hφ
      have hns : ¬ φ ∈ s := fun h => ha (hφ ▸ h)
      have hpos : 0 < φ (algebraMap (𝓞 K) K (∏ φ₀ ∈ s, alpha 𝔣 h𝔣 φ₀)) :=
        lt_of_le_of_ne (not_lt.mp (fun h => hns (ih.mp h))) hne.symm
      exact ⟨fun _ => Or.inl hφ, fun _ => mul_neg_of_neg_of_pos hneg hpos⟩
    · have hpos : 0 < φ (algebraMap (𝓞 K) K (alpha 𝔣 h𝔣 a)) := alpha_pos_of_ne 𝔣 h𝔣 hφ
      constructor
      · intro h
        exact Or.inr (ih.mp ((pos_iff_neg_of_mul_neg h).mp hpos))
      · rintro (h | h)
        · exact absurd h hφ
        · exact mul_neg_of_pos_of_neg hpos (ih.mpr h)

noncomputable def eps (ψ : HeightOneSpectrum (𝓞 K) → M) (φ₀ : K →+* ℝ) : M :=
  raySymbol K ψ (pI (alpha 𝔣 h𝔣 φ₀))

variable (ψ : HeightOneSpectrum (𝓞 K) → M)
  (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1)

include hψ in
theorem eps_mul_self (φ₀ : K →+* ℝ) : eps 𝔣 h𝔣 ψ φ₀ * eps 𝔣 h𝔣 ψ φ₀ = 1 := by
  have h0 := alpha_ne_zero 𝔣 h𝔣 φ₀
  rw [eps, ← raySymbol_pI_mul ψ h0 h0]
  apply hψ _ (mul_ne_zero h0 h0) (mul_sub_one_mem (alpha_sub_one_mem 𝔣 h𝔣 φ₀)
    (alpha_sub_one_mem 𝔣 h𝔣 φ₀))
  intro τ
  rw [map_mul, map_mul]
  exact mul_self_pos.mpr (realEmb_ne_zero τ h0)

include hψ in
theorem eps_inv (φ₀ : K →+* ℝ) : (eps 𝔣 h𝔣 ψ φ₀)⁻¹ = eps 𝔣 h𝔣 ψ φ₀ :=
  inv_eq_of_mul_eq_one_right (eps_mul_self 𝔣 h𝔣 ψ hψ φ₀)

include hψ in

theorem raySymbol_eq_prod {α : 𝓞 K} (hα : α ≠ 0) (hα1 : α - 1 ∈ 𝔣) :
    raySymbol K ψ (pI α) =
      ∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℝ => φ (algebraMap (𝓞 K) K α) < 0),
        eps 𝔣 h𝔣 ψ φ := by
  classical
  set s := Finset.univ.filter (fun φ : K →+* ℝ => φ (algebraMap (𝓞 K) K α) < 0) with hs
  obtain ⟨hp0, hp1, hpr⟩ := prod_ne_zero_and_sub_one_mem_and_raySymbol ψ 𝔣 s (alpha 𝔣 h𝔣)
    (fun i _ => alpha_ne_zero 𝔣 h𝔣 i) (fun i _ => alpha_sub_one_mem 𝔣 h𝔣 i)

  have hγ : raySymbol K ψ (pI (α * ∏ φ₀ ∈ s, alpha 𝔣 h𝔣 φ₀)) = 1 := by
    apply hψ _ (mul_ne_zero hα hp0) (mul_sub_one_mem hα1 hp1)
    intro τ
    rw [map_mul, map_mul]
    have hiff := prod_alpha_lt_zero_iff 𝔣 h𝔣 ψ s τ
    have hne := realEmb_ne_zero τ hp0
    have hneα := realEmb_ne_zero τ hα
    by_cases hτ : τ (algebraMap (𝓞 K) K α) < 0
    · have hmem : τ ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hτ⟩
      exact mul_pos_of_neg_of_neg hτ (hiff.mpr hmem)
    · have hnmem : τ ∉ s := by rw [hs, Finset.mem_filter]; exact fun h => hτ h.2
      have h1 : 0 < τ (algebraMap (𝓞 K) K α) := lt_of_le_of_ne (not_lt.mp hτ) hneα.symm
      have h2 : 0 < τ (algebraMap (𝓞 K) K (∏ φ₀ ∈ s, alpha 𝔣 h𝔣 φ₀)) :=
        lt_of_le_of_ne (not_lt.mp (fun h => hnmem (hiff.mp h))) hne.symm
      exact mul_pos h1 h2
  rw [raySymbol_pI_mul ψ hα hp0, hpr] at hγ
  have : raySymbol K ψ (pI α) = (∏ i ∈ s, raySymbol K ψ (pI (alpha 𝔣 h𝔣 i)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hγ
  rw [this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  exact eps_inv 𝔣 h𝔣 ψ hψ φ

end Main

end SignedRaySol

open SignedRaySol in

theorem solution
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
    (ψ : HeightOneSpectrum (𝓞 K) → M) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1) :
    ∃ ε : (K →+* ℝ) → M, (∀ φ : K →+* ℝ, ε φ ^ 2 = 1) ∧
      ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
        raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
          ∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℝ => φ (algebraMap (𝓞 K) K α) < 0), ε φ :=
  ⟨eps 𝔣 h𝔣 ψ, fun φ => by rw [sq]; exact eps_mul_self 𝔣 h𝔣 ψ hψ φ,
    fun _ hα hα1 => raySymbol_eq_prod 𝔣 h𝔣 ψ hψ hα hα1⟩

end S_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos
end P2MW
export P2MW.S_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos (solution)
