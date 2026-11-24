-- Prove2me | solution 1 for GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:12.805687+00:00
-- url     : https://prove2.me/submissions/d723bb23-013a-4703-afac-f06201b302f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvd
import Theorems.Thm_GlobalTheory_pow_dvd_pow_mul_pow_of_homogeneous_relation
import Theorems.Thm_GlobalTheory_T_exists_valuationSubring_algClosed_not_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R →
      (∀ r, IsUnit (1 - u * r)) →
      (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨
        ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L)
          (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  intro R _ u x M hu hJ
  let T := Localization.Away (u * x)
  have hux : IsUnit (algebraMap R T (u * x)) := IsLocalization.Away.algebraMap_isUnit (u * x)
  rw [map_mul, IsUnit.mul_iff] at hux
  obtain ⟨huT, hxT⟩ := hux
  obtain ⟨y, hy⟩ := hxT.exists_right_inv
  let t : T := algebraMap R T u ^ M * y
  have ht : algebraMap R T x * t = algebraMap R T u ^ M := by
    simp only [t]
    linear_combination (algebraMap R T u ^ M) * hy
  let S := Algebra.adjoin R ({t} : Set T)
  by_cases hS : IsUnit (algebraMap R S u)
  · left
    obtain ⟨⟨z, hz⟩, hz1⟩ := hS.exists_right_inv
    have hz2 : algebraMap R T u * z = 1 := congrArg Subtype.val hz1
    have hz' := hz
    simp only [S] at hz'
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨p, hp⟩ := hz'
    have hp' : aeval t p = z := hp
    set q : R[X] := 1 - C u * p with hq
    have hq0 : aeval t q = 0 := by
      simp [hq, hp', hz2]
    have hc : IsUnit (q.coeff 0) := by
      simpa [hq] using hJ (p.coeff 0)
    have hsum : algebraMap R T
        (∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i * (u ^ M) ^ i * x ^ (q.natDegree - i)) = 0 := by
      have h1 : algebraMap R T x ^ q.natDegree * aeval t q = 0 := by rw [hq0, mul_zero]
      rw [aeval_eq_sum_range, Finset.mul_sum] at h1
      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      rw [he, Nat.add_sub_cancel_left, Algebra.smul_def]
      simp only [map_mul, map_pow]
      rw [← ht]
      ring
    obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (u * x)) T _).1 hsum
    simp only [mul_pow, mul_assoc] at hN
    have hN' := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hu N)).1 hN
    refine ⟨M * (N + q.natDegree), fun j => ?_⟩
    rw [pow_mul, pow_mul]
    refine pow_dvd_pow_mul_pow_of_homogeneous_relation (u ^ M) x q.coeff _ N hc ?_ j
    simpa only [mul_assoc] using hN'
  · right
    obtain ⟨L, _, _, V, f, hf1, hf2⟩ := GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit S _ hS
    refine ⟨L, inferInstance, inferInstance, V, f.comp (algebraMap R S), ?_, hf1, ?_⟩
    · refine hf2 _ (mem_nonZeroDivisors_iff_right.2 fun s hs => ?_)
      have h1 : (s : T) * algebraMap R T u = 0 := congrArg Subtype.val hs
      exact Subtype.ext (huT.mul_left_eq_zero.1 h1)
    · refine ⟨f ⟨t, Algebra.self_mem_adjoin_singleton R t⟩, ?_⟩
      simp only [RingHom.comp_apply]
      rw [← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext ht.symm
end GlobalTheory
