-- Prove2me | solution 1 for Helfgott.noncoprime_compact_vonMangoldt_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T07:27:17.337062+00:00
-- url     : https://prove2.me/submissions/ea6db3a5-11a6-4688-b27a-331b6889e1a7

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Finset
open scoped BigOperators

namespace Helfgott

theorem noncoprime_vonMangoldt_mass_le (q K : ℕ) (hq : 0<q)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0≤A) (hw : ∀ n<2^K,|w n|≤A) :
    (∑ n ∈ range (2^K),if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) ≤ A*(K:ℝ)*Real.log (q:ℝ) := by
  classical
  let S := (range (2^K)).filter (fun n => ¬Nat.Coprime n q ∧ IsPrimePow n)
  have hs : S ⊆ (q^K).divisors := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn,hcop,hpow⟩
    have hnR : n<2^K := mem_range.mp hn
    obtain ⟨p,k,hp,hk,hpn⟩ := (isPrimePow_nat_iff n).mp hpow
    have hnot : ¬Nat.Coprime p q := by
      intro h
      exact hcop (hpn ▸ h.pow_left k)
    have hpd : p∣q := by
      by_contra! h
      exact hnot (hp.coprime_iff_not_dvd.mpr h)
    have h2 : 2^k≤n := by
      rw [← hpn]
      exact Nat.pow_le_pow_left hp.two_le k
    have hkK : k<K := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp
      (h2.trans_lt hnR)
    exact Nat.mem_divisors.mpr ⟨hpn ▸ pow_dvd_pow_of_dvd_of_le hpd hkK.le,
      pow_ne_zero K hq.ne'⟩
  have he : (∑ n ∈ range (2^K),if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) =
      ∑ n ∈ S,ArithmeticFunction.vonMangoldt n*|w n| := by
    rw [show S=(range (2^K)).filter (fun n => ¬Nat.Coprime n q ∧ IsPrimePow n) from rfl,
      Finset.sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hcop : Nat.Coprime n q
    · simp [hcop]
    · by_cases hpow : IsPrimePow n
      · simp [hcop,hpow]
      · have hz : ArithmeticFunction.vonMangoldt n=0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
        simp [hcop,hpow,hz]
  calc
    _ = ∑ n ∈ S,ArithmeticFunction.vonMangoldt n*|w n| := he
    _ ≤ ∑ n ∈ S,A*ArithmeticFunction.vonMangoldt n := by
      apply sum_le_sum
      intro n hn
      have hb := hw n (mem_range.mp (mem_filter.mp hn).1)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
        (ArithmeticFunction.vonMangoldt_nonneg (n:=n))
    _ = A*(∑ n ∈ S,ArithmeticFunction.vonMangoldt n) := by rw [Finset.mul_sum]
    _ ≤ A*(∑ n ∈ (q^K).divisors,ArithmeticFunction.vonMangoldt n) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact sum_le_sum_of_subset_of_nonneg hs (fun n hn hnot =>
        ArithmeticFunction.vonMangoldt_nonneg)
    _ = A*(K:ℝ)*Real.log (q:ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_sum,Nat.cast_pow,Real.log_pow]
      ring

end Helfgott


namespace Helfgott

theorem noncoprime_compact_vonMangoldt_mass_le (q K : ℕ) (hq : 0<q)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0≤A) (hw : ∀ n<2^K,|w n|≤A)
    (hzero : ∀ n,2^K≤n → w n=0) :
    (∑' n : ℕ,if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) ≤ A*(K:ℝ)*Real.log (q:ℝ) := by
  classical
  have he : (∑' n : ℕ,if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) =
      ∑ n ∈ range (2^K),if Nat.Coprime n q then (0:ℝ) else
        ArithmeticFunction.vonMangoldt n*|w n| := by
    apply tsum_eq_sum
    intro n hn
    have hnK : 2^K≤n := by simpa only [mem_range,not_lt] using hn
    rw [hzero n hnK]
    simp
  rw [he]
  exact noncoprime_vonMangoldt_mass_le q K hq w A hA hw

end Helfgott
end

open Finset
open scoped BigOperators

theorem solution (q K : ℕ) (hq : 0<q)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0≤A) (hw : ∀ n<2^K,|w n|≤A)
    (hzero : ∀ n,2^K≤n → w n=0) :
    (∑' n : ℕ,if Nat.Coprime n q then (0:ℝ) else
      ArithmeticFunction.vonMangoldt n*|w n|) ≤ A*(K:ℝ)*Real.log (q:ℝ) := Helfgott.noncoprime_compact_vonMangoldt_mass_le q K hq w A hA hw hzero

#print axioms solution
