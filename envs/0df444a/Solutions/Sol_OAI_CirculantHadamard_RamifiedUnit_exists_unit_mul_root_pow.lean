-- Prove2me | solution 1 for OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:41:08.677696+00:00
-- url     : https://prove2.me/submissions/78324ca1-4388-4ebe-a3b5-de4444cb8e9d

import Mathlib

open Polynomial

theorem puf_aux {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f - X ^ f.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i f.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact hcoeff i h
    · subst h; rw [if_pos rfl]; have := hf.coeff_natDegree; rw [this, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g.coeff 0 = 1 := by
    have := congrArg (fun p => p.coeff 0) hg
    simp only [coeff_sub, coeff_X_pow, coeff_C_mul, hzero] at this
    rw [if_neg hdeg.ne] at this
    have h2 : a * (g.coeff 0 - 1) = 0 := by rw [mul_sub, ← this]; ring
    have := (mul_eq_zero.1 h2).resolve_left ha
    exact sub_eq_zero.1 this
  have hX : X ∣ g - 1 := by
    rw [X_dvd_iff, coeff_sub, hg0, coeff_one_zero, sub_self]
  obtain ⟨q, hq⟩ := hX
  refine ⟨q, ?_⟩
  rw [← hq, add_sub_cancel, ← hg, add_sub_cancel]

theorem solution {R : Type*} {S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [IsLocalRing S]
    (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := puf_aux f a ha hf hdeg hzero hcoeff
  rw [hq] at hroot
  simp only [map_add, map_pow, aeval_X, map_mul, aeval_C, map_one] at hroot
  have hu : IsUnit (1 + z * aeval z q) := by
    by_contra hn
    have h1 : 1 + z * aeval z q ∈ IsLocalRing.maximalIdeal S := hn
    have h2 : z * aeval z q ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_right _ _ hz
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      simpa using Ideal.sub_mem _ h1 h2
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨-hu.unit⁻¹, ?_⟩
  have key : algebraMap R S a * (1 + z * aeval z q) = -z ^ f.natDegree := by
    linear_combination hroot
  calc algebraMap R S a = algebraMap R S a * (1 + z * aeval z q) * ↑hu.unit⁻¹ := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    _ = _ := by rw [key]; simp; ring
