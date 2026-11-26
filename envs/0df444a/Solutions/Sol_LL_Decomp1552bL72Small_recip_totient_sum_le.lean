-- Prove2me | solution 1 for LL_Decomp1552bL72Small.recip_totient_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T15:26:20.149944+00:00
-- url     : https://prove2.me/submissions/64f6334b-f836-4680-a9bc-b07368c238c7

import Mathlib

open Finset Real
open scoped Classical

namespace LL_Decomp1552bL72Small
end LL_Decomp1552bL72Small
open LL_Decomp1552bL72Small


namespace LL_Decomp1552bL72Small.Proof_LL_Decomp1552bL72Small_recip_totient_sum_le

/-- `1 / φ(m)` expanded over the sets of prime divisors of `m`. -/
theorem recip_totient (m : ℕ) (hm : m ≠ 0) :
    (1 : ℝ) / m.totient
      = 1 / m * ∑ S ∈ m.primeFactors.powerset, ∏ p ∈ S, (1 / ((p : ℝ) - 1)) := by
  rw [← Finset.prod_one_add]
  have hgt : ∀ p ∈ m.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := fun p hp => by
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have e : ((∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p hp => by
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one])
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors m)
  simp only [Nat.cast_mul] at h
  rw [e, Nat.cast_prod] at h
  have hf : ∏ p ∈ m.primeFactors, (1 + 1 / ((p : ℝ) - 1))
      = (∏ p ∈ m.primeFactors, (p : ℝ)) / ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have : (p : ℝ) - 1 ≠ 0 := (hgt p hp).ne'
    field_simp
    ring
  rw [hf]
  have hq : (0 : ℝ) < ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hgt
  have hφ : (0 : ℝ) < m.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [div_mul_div_comm, one_mul, div_eq_div_iff hφ.ne' (mul_pos hm' hq).ne', one_mul, ← h]
  ring

theorem sum_multiples (N d : ℕ) (hd : d ≠ 0) :
    ∑ m ∈ (Finset.Ico 1 N).filter (d ∣ ·), (1 : ℝ) / m
      ≤ 1 / d * ∑ k ∈ Finset.Ico 1 N, (1 : ℝ) / k := by
  have hsub : (Finset.Ico 1 N).filter (d ∣ ·) ⊆ (Finset.Ico 1 N).image (d * ·) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ico] at hm
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hm
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ico.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_ne_zero (fun h => by simp [h] at h1)
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hd)) h2
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
    (le_of_eq ?_)
  rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) h),
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [Nat.cast_mul, one_div_mul_one_div])

theorem harmonic_below (D : ℝ) (hD : 1 ≤ D) :
    ∑ k ∈ Finset.Ico 1 ⌈D⌉₊, (1 : ℝ) / k ≤ 1 + Real.log D := by
  have e : ∑ k ∈ Finset.Ico 1 ⌈D⌉₊, (1 : ℝ) / k = (harmonic (⌈D⌉₊ - 1) : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    unfold harmonic
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by rw [one_div, add_comm])
  rw [e]
  refine (harmonic_le_one_add_log _).trans ?_
  have : Real.log ((⌈D⌉₊ - 1 : ℕ) : ℝ) ≤ Real.log D := by
    by_cases h0 : ⌈D⌉₊ - 1 = 0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hD
    · refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) ?_
      have := Nat.ceil_lt_add_one (a := D) (by linarith)
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
  linarith

theorem telescope (M : ℕ) :
    ∑ i ∈ Finset.range M, (1 : ℝ) / (((i : ℝ) + 2) * ((i : ℝ) + 1)) = 1 - 1 / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have a : (n : ℝ) + 1 ≠ 0 := by positivity
    have b : (n : ℝ) + 2 ≠ 0 := by positivity
    have c : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem prime_sum (N : ℕ) :
    ∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : (Finset.range N).filter Nat.Prime ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Ico.mpr ⟨hp.2.two_le, by omega⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => ?_)).trans ?_
  · have : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
  · have e : ∑ n ∈ Finset.Ico 2 (N + 2), (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
        = ∑ i ∈ Finset.range N, (1 : ℝ) / (((i : ℝ) + 2) * ((i : ℝ) + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [e, telescope]
    have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
    linarith

end LL_Decomp1552bL72Small.Proof_LL_Decomp1552bL72Small_recip_totient_sum_le

open LL_Decomp1552bL72Small.Proof_LL_Decomp1552bL72Small_recip_totient_sum_le

theorem solution (D : ℝ) (hD : 1 ≤ D) :
    ∑ m ∈ Ico 1 ⌈D⌉₊, (1 / (m.totient : ℝ)) ≤ 3 * (log D + 1) := by
  set N := ⌈D⌉₊ with hN
  set P := (Finset.range N).filter Nat.Prime with hPdef
  have hP2 : ∀ S ∈ P.powerset, ∀ p ∈ S, p.Prime := fun S hS p hp =>
    (Finset.mem_filter.mp (Finset.mem_powerset.mp hS hp)).2
  have hw : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, (1 / ((p : ℝ) - 1)) := by
    intro S hS
    refine Finset.prod_nonneg (fun p hp => ?_)
    have : (1 : ℝ) < p := by exact_mod_cast (hP2 S hS p hp).one_lt
    exact div_nonneg zero_le_one (by linarith)
  -- expand each term over sets of primes, then enlarge to all `S` whose product divides `m`
  have step1 : ∑ m ∈ Finset.Ico 1 N, (1 / (m.totient : ℝ))
      ≤ ∑ m ∈ Finset.Ico 1 N, ∑ S ∈ P.powerset,
          if (∏ p ∈ S, p) ∣ m then 1 / (m : ℝ) * ∏ p ∈ S, (1 / ((p : ℝ) - 1)) else 0 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ico.mp hm).1; omega
    rw [recip_totient m hm0, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) (fun S hS _ => ?_)
    · rw [Finset.mem_powerset] at hS
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun p hp => ?_, (Finset.prod_dvd_prod_of_subset _ _ _ hS).trans
        (Nat.prod_primeFactors_dvd m)⟩
      have hpm := hS hp
      rw [hPdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (Nat.le_of_mem_primeFactors hpm) (Finset.mem_Ico.mp hm).2,
        Nat.prime_of_mem_primeFactors hpm⟩
    · exact mul_nonneg (by positivity) (hw S (Finset.mem_filter.mp hS).1)
  have step2 : ∀ S ∈ P.powerset,
      (∑ m ∈ Finset.Ico 1 N,
          if (∏ p ∈ S, p) ∣ m then 1 / (m : ℝ) * ∏ p ∈ S, (1 / ((p : ℝ) - 1)) else 0)
        ≤ (1 + Real.log D) * ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro S hS
    have hd : (∏ p ∈ S, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p hp => (hP2 S hS p hp).ne_zero)
    have h1 := (sum_multiples N _ hd).trans
      (mul_le_mul_of_nonneg_left (harmonic_below D hD) (by positivity))
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    refine (mul_le_mul_of_nonneg_right h1 (hw S hS)).trans (le_of_eq ?_)
    have e : 1 / ((∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, (1 / ((p : ℝ) - 1))
        = ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun p _ => by rw [one_div, one_div, mul_inv])
    rw [← e]
    ring
  have step3 : ∑ S ∈ P.powerset, ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 3 := by
    rw [← Finset.prod_one_add]
    have h1 : ∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ ∏ p ∈ P, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
      · have : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        have : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
          div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
        linarith
      · rw [add_comm]; exact Real.add_one_le_exp _
    rw [← Real.exp_sum] at h1
    have h2 := Real.exp_le_exp.mpr (prime_sum N)
    have h3 := Real.exp_one_lt_d9
    exact h1.trans (h2.trans (by linarith))
  have hlog : 0 ≤ 1 + Real.log D := by have := Real.log_nonneg hD; linarith
  calc ∑ m ∈ Finset.Ico 1 N, (1 / (m.totient : ℝ))
      ≤ _ := step1
    _ = ∑ S ∈ P.powerset, ∑ m ∈ Finset.Ico 1 N,
          if (∏ p ∈ S, p) ∣ m then 1 / (m : ℝ) * ∏ p ∈ S, (1 / ((p : ℝ) - 1)) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ S ∈ P.powerset, (1 + Real.log D) * ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.sum_le_sum step2
    _ = (1 + Real.log D) * ∑ S ∈ P.powerset, ∏ p ∈ S, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        rw [Finset.mul_sum]
    _ ≤ (1 + Real.log D) * 3 := mul_le_mul_of_nonneg_left step3 hlog
    _ = 3 * (Real.log D + 1) := by ring
