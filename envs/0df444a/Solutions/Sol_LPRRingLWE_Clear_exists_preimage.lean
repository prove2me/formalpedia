-- Prove2me | solution 1 for LPRRingLWE.Clear.exists_preimage
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:20:42.725041+00:00
-- url     : https://prove2.me/submissions/3d8f34c2-6174-46ef-b485-dc83136b148b

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

set_option autoImplicit false
open NumberField LPRRingLWE.Clear
open scoped nonZeroDivisors

theorem solution {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I) (M : FractionalIdeal (𝓞 K)⁰ K)
    (c : K) (hc : c ∈ cleared t I) (hc1 : c - 1 ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ∀ v ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * M,
      (∃ w ∈ M, c * v = algebraMap (𝓞 K) K t * w) ∧
        c * v - v ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * J * M := by
  intro v hv
  have hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro h
    exact hI (by simpa using h)
  constructor
  · obtain ⟨i, hi, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hc
    have hmem := FractionalIdeal.mul_mem_mul hi hv
    have : (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * ((I : FractionalIdeal (𝓞 K)⁰ K) * M) = M := by
      rw [← mul_assoc, inv_mul_cancel₀ hI0, one_mul]
    rw [this] at hmem
    exact ⟨i * v, hmem, by ring⟩
  · have hmem := FractionalIdeal.mul_mem_mul hc1 hv
    have e : c * v - v = (c - 1) * v := by ring
    rw [e]
    have : (J : FractionalIdeal (𝓞 K)⁰ K) * ((I : FractionalIdeal (𝓞 K)⁰ K) * M)
        = (I : FractionalIdeal (𝓞 K)⁰ K) * J * M := by
      ring
    rwa [this] at hmem
