-- Prove2me | solution 1 for LPRRingLWE.Clear.mem_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:16:12.26835+00:00
-- url     : https://prove2.me/submissions/1d583392-93e2-4e63-ab87-b3f299a3ba45

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

set_option autoImplicit false
open NumberField LPRRingLWE.Clear
open scoped nonZeroDivisors

theorem solution {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I) (hcop : ClearedCoprime t I J)
    (M : FractionalIdeal (𝓞 K)⁰ K) :
    ∀ u ∈ M, algebraMap (𝓞 K) K t * u ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * J * M →
      u ∈ (J : FractionalIdeal (𝓞 K)⁰ K) * M := by
  intro u hu htu
  have hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro h
    exact hI (by simpa using h)
  have h1 : (1 : K) ∈ cleared t I + (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hcop.2]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, by simp⟩
  obtain ⟨c, hc, j, hj, hcj⟩ := (FractionalIdeal.mem_add _ _ _).mp h1
  obtain ⟨i, hi, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hc
  have e : u = (i * (algebraMap (𝓞 K) K t * u)) + j * u := by
    calc u = (algebraMap (𝓞 K) K t * i + j) * u := by rw [hcj]; ring
      _ = _ := by ring
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · have hmem := FractionalIdeal.mul_mem_mul hi htu
    have : (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * ((I : FractionalIdeal (𝓞 K)⁰ K) * J * M)
        = (J : FractionalIdeal (𝓞 K)⁰ K) * M := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hI0, one_mul]
    rwa [this] at hmem
  · exact FractionalIdeal.mul_mem_mul hj hu
