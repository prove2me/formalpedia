-- Prove2me | solution 1 for GlobalTheory.CMLattice.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:57.072875+00:00
-- url     : https://prove2.me/submissions/1ee9cad8-d4d9-4ba2-a8d1-fc2cd4389a8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Theorems.Thm_GlobalTheory_CMLattice_exists_im_ne_zero
import Theorems.Thm_P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8

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
theorem _root_.solution (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) (L : PeriodPair)
    (hL : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) :
    ∃ (𝔞 : Ideal (𝓞 K)) (c : ℂ), 𝔞 ≠ ⊥ ∧ c ≠ 0 ∧
      ∀ z, z ∈ L.lattice ↔ ∃ a ∈ 𝔞, z = c * σ (a : K) := by
  obtain ⟨a, ha⟩ := exists_im_ne_zero σ hσ
  have hω : L.ω₁ ≠ 0 := ω₁_ne_zero L
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 (hL a _ L.ω₁_mem_lattice)
  have hn : (n : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at hmn
    have : σ (a : K) = m := (mul_right_cancel₀ hω hmn).symm
    rw [this] at ha
    simp at ha
  set t : K := ((a : K) - m) / n with ht
  have hσt : σ t * L.ω₁ = L.ω₂ := by
    rw [ht, map_div₀, map_sub, map_intCast, map_intCast, div_mul_eq_mul_div, div_eq_iff hn]
    linear_combination (-1 : ℂ) * hmn
  have hstab : ∀ (r : 𝓞 K) (p q : ℤ), ∃ p' q' : ℤ, (r : K) * (p + q * t) = p' + q' * t := by
    intro r p q
    have hmem : (p : ℂ) * L.ω₁ + q * L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.2 ⟨p, q, rfl⟩
    obtain ⟨p', q', hpq⟩ := PeriodPair.mem_lattice.1 (hL r _ hmem)
    refine ⟨p', q', σ.injective ?_⟩
    apply mul_right_cancel₀ hω
    simp only [map_mul, map_add, map_intCast]
    rw [← hσt] at hpq
    linear_combination (-1 : ℂ) * hpq
  obtain ⟨u, v, hv, htuv⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hV0 : (v : K) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
  have hσV : σ (v : K) ≠ 0 := (map_ne_zero σ).2 hV0
  have hu : (u : K) = (v : K) * t := by
    rw [← htuv]; field_simp
  let 𝔞 : Ideal (𝓞 K) :=
    { carrier := {x | ∃ p q : ℤ, (x : K) = (v : K) * (p + q * t)}
      add_mem' := by
        rintro x y ⟨p, q, hx⟩ ⟨p', q', hy⟩
        exact ⟨p + p', q + q', by
          rw [RingOfIntegers.coe_eq_algebraMap, map_add, ← RingOfIntegers.coe_eq_algebraMap,
            ← RingOfIntegers.coe_eq_algebraMap, hx, hy]
          push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro r x ⟨p, q, hx⟩
        obtain ⟨p', q', h'⟩ := hstab r p q
        refine ⟨p', q', ?_⟩
        rw [smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, ← RingOfIntegers.coe_eq_algebraMap,
          ← RingOfIntegers.coe_eq_algebraMap, hx, ← h']
        ring }
  have hmem𝔞 : ∀ x : 𝓞 K, x ∈ 𝔞 ↔ ∃ p q : ℤ, (x : K) = (v : K) * (p + q * t) := fun x => Iff.rfl
  refine ⟨𝔞, L.ω₁ / σ (v : K), ?_, div_ne_zero hω hσV, ?_⟩
  · intro hbot
    have h1 : v ∈ 𝔞 := (hmem𝔞 v).2 ⟨1, 0, by simp⟩
    rw [hbot] at h1
    exact hv0 ((Submodule.mem_bot _).1 h1)
  · intro z
    constructor
    · intro hz
      obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 hz
      refine ⟨v * p + q * u, (hmem𝔞 _).2 ⟨p, q, ?_⟩, ?_⟩
      · rw [RingOfIntegers.coe_eq_algebraMap]
        simp only [map_add, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, hu]
        ring
      · rw [RingOfIntegers.coe_eq_algebraMap]
        simp only [map_add, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, hu]
        rw [← hσt]
        field_simp
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, q, hpq⟩ := (hmem𝔞 x).1 hx
      refine PeriodPair.mem_lattice.2 ⟨p, q, ?_⟩
      rw [hpq, ← hσt]
      simp only [map_mul, map_add, map_intCast]
      field_simp
end GlobalTheory.CMLattice
