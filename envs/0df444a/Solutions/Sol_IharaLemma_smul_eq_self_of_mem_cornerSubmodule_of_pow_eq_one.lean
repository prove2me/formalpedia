-- Prove2me | solution 1 for IharaLemma.smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1decf1d7-5436-5092-aa76-9d9c6cb45346

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one

set_option autoImplicit false

namespace CohL2
namespace CornerTriv

theorem eq_one_of_pow_eq_one {R : Type} [CommRing R] [IsLocalRing R] (x : R) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) (hx : x ^ n = 1) (h1 : x - 1 ∈ IsLocalRing.maximalIdeal R) : x = 1 := by
  have hgeom : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := geom_sum_mul x n

  have hdiff : (∑ i ∈ Finset.range n, x ^ i) - (n : R) ∈ IsLocalRing.maximalIdeal R := by
    have : (∑ i ∈ Finset.range n, x ^ i) - (n : R) = ∑ i ∈ Finset.range n, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hdvd : x - 1 ∣ x ^ i - 1 := sub_one_dvd_pow_sub_one x i
    exact Ideal.mem_of_dvd _ hdvd h1
  have hunit : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range n, x ^ i) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hnmem : (n : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hmem hdiff
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hnmem hn
  have h0 : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = 0 := by rw [hgeom, hx, sub_self]
  have := hunit.mul_right_eq_zero.mp h0
  exact sub_eq_zero.mp this

end CohL2.CornerTriv

open CohL2.CornerTriv in
theorem solution
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) (t : B) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : B)) (ht : t ^ n = 1) (h1 : t - 1 ∈ S.𝔪 i)
    (v : M) (hv : v ∈ IharaLemma.cornerSubmodule (M := M) (S.e i)) :
    t • v = v := by
  set x : S.CornerRing i := algebraMap B (S.CornerRing i) t with hxdef
  have hxn : x ^ n = 1 := by rw [hxdef, ← map_pow, ht, map_one]
  have hx1 : x - 1 ∈ IsLocalRing.maximalIdeal (S.CornerRing i) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (S.𝔪 i) (S.CornerRing i), hxdef,
      ← map_one (algebraMap B (S.CornerRing i)), ← map_sub]
    exact Ideal.mem_map_of_mem _ h1
  have hnC : IsUnit ((n : ℕ) : S.CornerRing i) := by
    simpa using hn.map (algebraMap B (S.CornerRing i))
  have hx : x = 1 := eq_one_of_pow_eq_one x n hnC hxn hx1

  have hB : S.e i * t * S.e i = S.e i := by
    have h := congrArg (fun z : S.CornerRing i => (z : B)) hx
    simp only [hxdef, IharaLemma.IdempotentSplitting.algebraMap_cornerRing_coe,
      IharaLemma.IdempotentSplitting.coe_one_cornerRing] at h
    exact h
  have hte : t * S.e i = S.e i := by
    calc t * S.e i = S.e i * t * S.e i := by rw [mul_comm (S.e i) t, mul_assoc, (S.idem i).eq]
      _ = S.e i := hB
  obtain ⟨w, rfl⟩ := hv
  show t • (S.e i • (LinearMap.id (R := B) w)) = S.e i • (LinearMap.id (R := B) w)
  rw [smul_smul, hte]

end S_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
end P2MW
export P2MW.S_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one (solution)
