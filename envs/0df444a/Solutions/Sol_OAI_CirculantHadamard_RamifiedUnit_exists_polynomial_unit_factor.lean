-- Prove2me | solution 1 for OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:40:36.458782+00:00
-- url     : https://prove2.me/submissions/c549f0c2-531f-45ef-80cb-348b5deaef7f

import Mathlib

open Polynomial

theorem solution {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) (a : R) (ha : a ≠ 0)
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
