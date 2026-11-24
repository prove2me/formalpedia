-- Prove2me | solution 1 for GlobalTheory.CMLattice.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:59.045823+00:00
-- url     : https://prove2.me/submissions/9e8b3f30-6c01-4dad-8052-6cf1e96e93f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume

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
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMLattice
theorem _root_.solution (σ : K →+* ℂ) (L L' : PeriodPair) (𝔟 : Ideal (𝓞 K)) (β : ℂ) (h𝔟 : 𝔟 ≠ ⊥)
    (hβ : β ≠ 0)
    (h1 : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice,
      β * σ x * z ∈ L'.lattice)
    (h2 : ∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) (z : ℂ) :
    z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice := by
  constructor
  · intro hz y hy
    exact h2 y hy z hz
  · intro hz
    have hb0 : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
    have h1mem : (1 : K) ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * 𝔟 := by
      rw [inv_mul_cancel₀ hb0]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : σ 1 * z ∈ L'.lattice := by
      refine FractionalIdeal.mul_induction_on (C := fun w => σ w * z ∈ L'.lattice) h1mem ?_ ?_
      · intro x hx y hy
        obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
        have hx' : ∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K)) := by
          intro b hb
          obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hb0).1 hx _
            ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
          rw [RingOfIntegers.coe_eq_algebraMap, ← hr]
          exact RingOfIntegers.isIntegral_coe r
        have hmem := h1 x hx' _ (hz y' hy')
        have e : σ (x * algebraMap (𝓞 K) K y') * z = β * σ x * (β⁻¹ * σ (y' : K) * z) := by
          rw [map_mul, RingOfIntegers.coe_eq_algebraMap]
          field_simp
        show σ (x * algebraMap (𝓞 K) K y') * z ∈ L'.lattice
        rw [e]
        exact hmem
      · intro x y hx hy
        show σ (x + y) * z ∈ L'.lattice
        rw [map_add, add_mul]
        exact add_mem hx hy
    simpa using key
end GlobalTheory.CMLattice
