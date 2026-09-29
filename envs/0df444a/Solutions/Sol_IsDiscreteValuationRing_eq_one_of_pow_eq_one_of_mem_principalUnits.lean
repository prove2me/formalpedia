-- Prove2me | solution 1 for IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7fafdda4-a31f-5141-841b-cfdc63eea9cd

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits

set_option autoImplicit false
open IsLocalRing

namespace Ws26U8

theorem exists_one_add_pow_eq_quadratic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(n : R) + c + x * c, ?_⟩
    rw [pow_succ, hc]
    push_cast
    ring

end Ws26U8

open IsLocalRing Ws26U8 in
theorem solution {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} {e : ℕ} (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {ζ : Rˣ} (hζ : ζ ∈ principalUnits R k) (hζn : ζ ^ n = 1) : ζ = 1 := by
  by_contra hζne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ n = Ideal.span {π ^ n} := fun n => by
    rw [hmax, Ideal.span_singleton_pow]

  rw [hpow, Ideal.span_singleton_eq_span_singleton] at hne
  obtain ⟨c, hc⟩ := hne.symm

  set x : R := (ζ : R) - 1 with hx_def
  have hx0 : x ≠ 0 := by
    intro h; apply hζne; ext; rw [Units.val_one]; exact sub_eq_zero.mp h
  obtain ⟨j, w, hxw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hjk : k ≤ j := by
    have h : π ^ k ∣ x := by
      have := hζ; rw [mem_principalUnits_iff, hpow, Ideal.mem_span_singleton] at this; exact this
    rw [hxw, mul_comm] at h
    have h' : π ^ k ∣ π ^ j := (Units.dvd_mul_right.mp h)
    exact (pow_dvd_pow_iff hπ0 hπ.not_isUnit).mp h'

  obtain ⟨d, hd⟩ := exists_one_add_pow_eq_quadratic x n
  have hζ1 : (ζ : R) = 1 + x := by rw [hx_def]; ring
  have hzero : (n : R) * x + x ^ 2 * d = 0 := by
    have h := congrArg Units.val hζn
    rw [Units.val_pow_eq_pow_val, Units.val_one, hζ1, hd] at h
    linear_combination h

  obtain ⟨m, hm⟩ : ∃ m, j = e + m + 1 := ⟨j - e - 1, by omega⟩
  subst hm
  have hfac : (n : R) * x + x ^ 2 * d
      = π ^ (e + (e + m + 1)) * ((c : R) * w + π ^ (m + 1) * (w ^ 2 * d)) := by
    rw [← hc, hxw]
    ring
  have hunit : IsUnit ((c : R) * w + π ^ (m + 1) * (w ^ 2 * d)) := by

    have hmem : π ^ (m + 1) * (w ^ 2 * d) ∈ IsLocalRing.maximalIdeal R := by
      rw [hmax]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) _ (Nat.succ_pos m))
    by_contra hnu
    have hsum : (c : R) * w ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (c : R) * w + π ^ (m + 1) * (w ^ 2 * d) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      simpa using (IsLocalRing.maximalIdeal R).sub_mem h2 hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hsum (c.isUnit.mul w.isUnit)
  rw [hfac] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact pow_ne_zero _ hπ0 h
  · exact hunit.ne_zero h

end S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits
end P2MW
export P2MW.S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits (solution)
