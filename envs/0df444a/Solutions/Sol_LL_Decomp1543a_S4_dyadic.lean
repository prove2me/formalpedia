-- Prove2me | solution 1 for LL_Decomp1543a.S4_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:25.678211+00:00
-- url     : https://prove2.me/submissions/1151292f-db8d-4967-aac0-8a4bb960b717

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_rangeN
import Definitions.Def_LL_Decomp1543a_Ssum
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_lam4
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner
import Definitions.Def_LL_Decomp1543a_block
import Definitions.Def_LL_Decomp1543a_Jn

open Real Finset ArithmeticFunction

namespace VaAAux

theorem two_pow_logb (y : ℝ) (hy : 0 < y) : (2 : ℝ) ^ (Real.log y / Real.log 2) = y :=
  Real.rpow_logb (by norm_num) (by norm_num) hy

open LL_Decomp1543a in
theorem Jn_le (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    (2 : ℝ) ^ (Jn N U V - 1) * V ≤ N / U := by
  have hUV0 : 0 < U * V := mul_pos hU hV
  have hy : 1 ≤ (N : ℝ) / (U * V) := by rw [le_div_iff₀ hUV0]; linarith
  have hx0 : 0 ≤ Real.log ((N : ℝ) / (U * V)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hy) (Real.log_pos (by norm_num)).le
  have h1 : Jn N U V - 1 = ⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ := by
    unfold Jn; omega
  have h2 : (2 : ℝ) ^ (Jn N U V - 1) ≤ (N : ℝ) / (U * V) := by
    rw [h1, ← Real.rpow_natCast]
    calc (2 : ℝ) ^ ((⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (Real.log ((N : ℝ) / (U * V)) / Real.log 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hx0)
      _ = (N : ℝ) / (U * V) := two_pow_logb _ (by linarith)
  calc (2 : ℝ) ^ (Jn N U V - 1) * V ≤ (N : ℝ) / (U * V) * V :=
        mul_le_mul_of_nonneg_right h2 hV.le
    _ = N / U := by field_simp

open LL_Decomp1543a in
theorem lt_two_pow_Jn (N : ℕ) (U V : ℝ) (hN : 0 < N) (hU : 0 < U) (hV : 0 < V) :
    (N : ℝ) / U < (2 : ℝ) ^ (Jn N U V) * V := by
  have hUV0 : 0 < U * V := mul_pos hU hV
  have hy : 0 < (N : ℝ) / (U * V) := by positivity
  have h1 : Real.log ((N : ℝ) / (U * V)) / Real.log 2 <
      ((⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have h2 : (N : ℝ) / (U * V) < (2 : ℝ) ^ (Jn N U V) := by
    have : Jn N U V = ⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ + 1 := rfl
    rw [this, ← Real.rpow_natCast]
    calc (N : ℝ) / (U * V) = (2 : ℝ) ^ (Real.log ((N : ℝ) / (U * V)) / Real.log 2) :=
          (two_pow_logb _ hy).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  calc (N : ℝ) / U = (N : ℝ) / (U * V) * V := by field_simp
    _ < (2 : ℝ) ^ (Jn N U V) * V := mul_lt_mul_of_pos_right h2 hV


theorem reindex_div (N : ℕ) (R : Finset ℕ) (hR : R ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → ℕ → ℂ) :
    ∑ n ∈ R, ∑ t ∈ n.divisors.filter P, g n t =
      ∑ t ∈ (Icc 1 N).filter P, ∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ R), g (m * t) t := by
  have h : ∀ (n t : ℕ), (n ∈ R ∧ t ∈ n.divisors.filter P) ↔
      (n ∈ R.filter (fun n => t ∣ n) ∧ t ∈ (Icc 1 N).filter P) := by
    intro n t
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨hn, ⟨htn, hn0⟩, hP⟩
      have h1 := mem_Icc.1 (hR hn)
      have h2 := Nat.le_of_dvd (by omega) htn
      exact ⟨⟨hn, htn⟩, ⟨Nat.pos_of_dvd_of_pos htn (by omega), by omega⟩, hP⟩
    · rintro ⟨⟨hn, htn⟩, ⟨ht, hP⟩⟩
      have h1 := mem_Icc.1 (hR hn)
      exact ⟨hn, ⟨htn, by omega⟩, hP⟩
  rw [sum_comm' h]
  apply sum_congr rfl
  intro t ht
  have ht0 : 0 < t := (mem_Icc.1 (mem_filter.1 ht).1).1
  apply sum_nbij' (fun n => n / t) (fun m => m * t)
  · intro n hn
    obtain ⟨hnR, htn⟩ := mem_filter.1 hn
    have h1 := mem_Icc.1 (hR hnR)
    refine mem_filter.2 ⟨mem_Icc.2 ⟨?_, (Nat.div_le_self n t).trans h1.2⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) htn) ht0
    · rw [Nat.div_mul_cancel htn]; exact hnR
  · intro m hm
    obtain ⟨_, hmR⟩ := mem_filter.1 hm
    exact mem_filter.2 ⟨hmR, dvd_mul_left t m⟩
  · intro n hn
    exact Nat.div_mul_cancel (mem_filter.1 hn).2
  · intro m _
    exact Nat.mul_div_cancel m ht0
  · intro n hn
    rw [Nat.div_mul_cancel (mem_filter.1 hn).2]

theorem dyad_sum (V : ℝ) (hV : 0 < V) (t : ℝ) (a : ℂ) (J : ℕ) :
    ∑ j ∈ range J, (if (2 ^ j * V < t ∧ t ≤ 2 * (2 ^ j * V)) then a else 0)
      = if (V < t ∧ t ≤ 2 ^ J * V) then a else 0 := by
  induction J with
  | zero =>
    rw [sum_range_zero]
    exact (if_neg (fun h => by simp only [pow_zero, one_mul] at h; linarith [h.1, h.2])).symm
  | succ J ih =>
    rw [sum_range_succ, ih]
    have hJ : V ≤ 2 ^ J * V := by
      have := one_le_pow₀ (M₀ := ℝ) (by norm_num : (1 : ℝ) ≤ 2) (n := J)
      nlinarith
    have h2 : (2 : ℝ) ^ (J + 1) * V = 2 * (2 ^ J * V) := by ring
    rw [h2]
    by_cases hA : V < t <;> by_cases hB : t ≤ 2 ^ J * V <;> by_cases hC : t ≤ 2 * (2 ^ J * V) <;>
      simp [hA, hB, hC] <;> linarith

end VaAAux

open LL_Decomp1543a in
theorem solution (c : ℝ) (N : ℕ) (U V α : ℝ) (hU : 0 < U) (hV : 0 < V) :
    Ssum (lam4 U V) c N α = ∑ j ∈ range (Jn N U V), block c N U (2 ^ j * V) α := by
  set D : ℕ → ℂ := fun t => (moebius t : ℂ) * inner c N U α t with hD
  have hL : Ssum (lam4 U V) c N α = ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => V < (t : ℝ)), D t := by
    unfold Ssum
    have step : ∀ n ∈ rangeN c N, ((lam4 U V n : ℝ) : ℂ) * e (α * n) =
        ∑ t ∈ n.divisors.filter (fun t : ℕ => V < (t : ℝ)),
          (moebius t : ℂ) * (am U (n / t) : ℂ) * e (α * n) := by
      intro n _
      unfold lam4
      push_cast
      rw [sum_mul]
    rw [sum_congr rfl step, VaAAux.reindex_div N (rangeN c N) (filter_subset _ _)
      (fun t : ℕ => V < (t : ℝ)) (fun n t => (moebius t : ℂ) * (am U (n / t) : ℂ) * e (α * n))]
    apply sum_congr rfl
    intro t ht
    have ht0 : 0 < t := (mem_Icc.1 (mem_filter.1 ht).1).1
    have hS : mRange c N U t = ((Icc 1 N).filter (fun m => m * t ∈ rangeN c N)).filter
        (fun m : ℕ => U < (m : ℝ)) := by
      ext m
      simp only [mRange, rangeN, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
        have : m ≤ m * t := Nat.le_mul_of_pos_right m ht0
        have : 1 ≤ m * t := by omega
        exact ⟨⟨⟨h1, h2⟩, ⟨⟨by omega, h4⟩, h3⟩⟩, h5⟩
      · rintro ⟨⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, h5⟩⟩, h6⟩
        exact ⟨⟨h1, h2⟩, h5, h4, h6⟩
    simp only [hD, LL_Decomp1543a.inner]
    rw [hS, mul_sum]
    symm
    rw [sum_filter_of_ne (p := fun m : ℕ => U < (m : ℝ))]
    · apply sum_congr rfl
      intro m _
      rw [Nat.mul_div_cancel m ht0, mul_assoc]
    · intro m _ hm
      by_contra hmU
      apply hm
      have : am U m = 0 := by
        unfold am
        apply sum_eq_zero
        intro r hr
        obtain ⟨hr1, hr2⟩ := mem_filter.1 hr
        have hm0 : m ≠ 0 := (Nat.mem_divisors.1 hr1).2
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (Nat.dvd_of_mem_divisors hr1)
        exfalso
        have h3 : (r : ℝ) ≤ m := by exact_mod_cast this
        linarith [not_lt.1 hmU]
      rw [this]
      simp
  have hblock : ∀ j : ℕ, block c N U (2 ^ j * V) α =
      ∑ t ∈ Icc 1 N, if (2 ^ j * V < (t : ℝ) ∧ (t : ℝ) ≤ 2 * (2 ^ j * V)) then D t else 0 := by
    intro j
    unfold block tBlock
    rw [sum_filter]
  have hR : ∑ j ∈ range (Jn N U V), block c N U (2 ^ j * V) α =
      ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => V < (t : ℝ)), D t := by
    rw [sum_congr rfl (fun j _ => hblock j), sum_comm]
    simp_rw [VaAAux.dyad_sum V hV]
    rw [sum_filter]
    apply sum_congr rfl
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.1 ht).1
    have hN : 0 < N := by have := (mem_Icc.1 ht).2; omega
    by_cases hA : V < (t : ℝ)
    · by_cases hB : (t : ℝ) ≤ 2 ^ (Jn N U V) * V
      · simp [hA, hB]
      · rw [if_pos hA, if_neg (by tauto)]
        push Not at hB
        have hlt := VaAAux.lt_two_pow_Jn N U V hN hU hV
        rw [div_lt_iff₀ hU] at hlt
        have hz : mRange c N U t = ∅ := by
          ext m
          simp only [mRange, mem_filter, mem_Icc, Finset.notMem_empty, iff_false]
          rintro ⟨_, h3, h4, h5⟩
          have h6 : ((m : ℝ)) * t ≤ N := by exact_mod_cast h4
          have h7 : U * (2 ^ (Jn N U V) * V) < m * t :=
            mul_lt_mul'' h5 hB hU.le (by positivity)
          linarith
        simp only [hD, LL_Decomp1543a.inner, hz, sum_empty, mul_zero]
    · simp [hA]
  rw [hL, hR]
