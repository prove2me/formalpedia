-- Prove2me | solution 1 for GlobalTheory.lattice_cm_eq_ideal_and_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:39:40.894709+00:00
-- url     : https://prove2.me/submissions/cddf9e70-7cde-4e31-8000-8a7bcf811c32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Theorems.Thm_GlobalTheory_CMLattice_exists_ideal
import Theorems.Thm_GlobalTheory_CMLattice_covol_eq
import Theorems.Thm_GlobalTheory_CMLattice_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open CMLattice
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ →
  ∀ (L L' : PeriodPair), (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
  (∃ (𝔞 : Ideal (𝓞 K)) (c : ℂ), 𝔞 ≠ ⊥ ∧ c ≠ 0 ∧ ∀ z, z ∈ L.lattice ↔ ∃ a ∈ 𝔞, z = c * σ (a : K)) ∧
  ∀ (𝔟 : Ideal (𝓞 K)) (β : ℂ), 𝔟 ≠ ⊥ → β ≠ 0 →
    (∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice, β * σ x * z ∈ L'.lattice) →
    (∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) →
    (∀ z, z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice) ∧
    |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| * Ideal.absNorm 𝔟 = ‖β‖ ^ 2 * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  intro K _ _ hK σ hσ L L' hL
  refine ⟨exists_ideal σ hσ L hL, ?_⟩
  intro 𝔟 β h𝔟 hβ h1 h2
  have hmem := mem_iff σ L L' 𝔟 β h𝔟 hβ h1 h2
  refine ⟨hmem, ?_⟩
  obtain ⟨𝔞, c, -, hc, hLc⟩ := exists_ideal σ hσ L hL
  let b : Basis (Fin 2) ℤ (𝓞 K) :=
    Module.finBasisOfFinrankEq ℤ (𝓞 K) ((RingOfIntegers.rank K).trans hK)
  set A0 : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hA0
  set Bb : FractionalIdeal (𝓞 K)⁰ K := (𝔟 : FractionalIdeal (𝓞 K)⁰ K) with hBb
  have hb0 : Bb ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
  have hL1 : ∀ z, z ∈ L.lattice ↔ ∃ x ∈ A0, z = c * σ x := by
    intro z
    rw [hLc z]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      exact ⟨a, ha, rfl⟩
  have hL2 : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ Bb⁻¹ * A0, z = (β * c) * σ x := by
    intro z
    constructor
    · intro hz
      have h1mem : (1 : K) ∈ Bb⁻¹ * Bb := by
        rw [inv_mul_cancel₀ hb0]
        exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
      have key : ∃ x ∈ Bb⁻¹ * A0, σ 1 * z = (β * c) * σ x := by
        refine FractionalIdeal.mul_induction_on
          (C := fun w => ∃ x ∈ Bb⁻¹ * A0, σ w * z = (β * c) * σ x) h1mem ?_ ?_
        · intro x hx y hy
          obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
          obtain ⟨a, ha, hae⟩ := (hL1 _).1 ((hmem z).1 hz y' hy')
          refine ⟨x * a, FractionalIdeal.mul_mem_mul hx ha, ?_⟩
          rw [map_mul, map_mul]
          calc σ x * σ (algebraMap (𝓞 K) K y') * z
              = β * σ x * (β⁻¹ * σ (y' : K) * z) := by
                rw [RingOfIntegers.coe_eq_algebraMap]; field_simp
            _ = β * c * (σ x * σ a) := by rw [hae]; ring
        · rintro x y ⟨x1, hx1, e1⟩ ⟨y1, hy1, e2⟩
          exact ⟨x1 + y1, Submodule.add_mem (↑(Bb⁻¹ * A0) : Submodule (𝓞 K) K) hx1 hy1, by rw [map_add, add_mul, e1, e2, map_add]; ring⟩
      simpa using key
    · rintro ⟨x, hx, rfl⟩
      rw [hmem]
      intro y hy
      refine (hL1 _).2 ⟨(y : K) * x, ?_, ?_⟩
      · have hyx : (y : K) * x ∈ Bb * (Bb⁻¹ * A0) :=
          FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩) hx
        rwa [← mul_assoc, mul_inv_cancel₀ hb0, one_mul] at hyx
      · rw [map_mul]
        field_simp
  have hcL := covol_eq σ b L A0 c hc hL1
  have hcL' := covol_eq σ b L' (Bb⁻¹ * A0) (β * c) (mul_ne_zero hβ hc) hL2
  have hN : (Ideal.absNorm 𝔟 : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 h𝔟)
  rw [hcL, hcL', map_mul, map_inv₀, hA0, hBb, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.coeIdeal_absNorm, norm_mul]
  push_cast
  field_simp
end GlobalTheory
