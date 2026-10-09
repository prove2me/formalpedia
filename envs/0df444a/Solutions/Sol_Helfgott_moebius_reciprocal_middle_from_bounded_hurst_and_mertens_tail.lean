-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T03:08:33.713893+00:00
-- url     : https://prove2.me/submissions/6335ab49-f6a2-4d87-bbaa-a271dc1933b4

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_Helfgott_moebius_initial_integral_le_303

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem reciprocal_middle_assembled_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma reciprocal_middle_assembled_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma reciprocal_middle_assembled_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem reciprocal_middle_assembled_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,reciprocal_middle_assembled_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [reciprocal_middle_assembled_floorRoot_two_eq_one_iff_squarefree n hn]

lemma reciprocal_middle_assembled_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,reciprocal_middle_assembled_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem reciprocal_middle_assembled_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast reciprocal_middle_assembled_coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast reciprocal_middle_assembled_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem reciprocal_middle_assembled_moebius_real_logarithmic_kernel_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d∈Finset.Icc 1 (Nat.floor x),∑ k∈Finset.Icc 1 ((Nat.floor x)/d),
      ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x := by
  let N := Nat.floor x
  have hN : 1 ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  change (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
    ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x
  have hr := reciprocal_middle_assembled_finite_positive_divisor_reindex N
    (fun d k => ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ)))
  have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (∑ d∈n.divisors,((moebius d : ℤ) : ℝ)*Real.log (x/((d*(n/d) : ℕ) : ℝ))) =
        (if n=1 then (1:ℝ) else 0)*Real.log (x/(n : ℝ)) := by
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1;omega
    have hemul : ∀ d∈n.divisors,d*(n/d)=n := fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [Finset.sum_congr rfl (fun d hd => by rw [hemul d hd]),←Finset.sum_mul]
    have hm : (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then 1 else 0 := by
      exact_mod_cast reciprocal_middle_assembled_moebius_divisor_sum n hn0
    rw [hm]
  rw [←hr,Finset.sum_congr rfl he]
  simp [Finset.mem_Icc,hN]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_middle_assembled_reciprocal_rectangle_intervalIntegrable (a b l r : ℝ) (ha : 0 < a) :
    IntervalIntegrable (fun t : ℝ => if a ≤ t ∧ t ≤ b then t⁻¹ else 0)
      volume l r := by
  have hm : Measurable (fun t : ℝ => if a ≤ t ∧ t ≤ b then t⁻¹ else 0) :=
    Measurable.ite (measurableSet_Ici.inter measurableSet_Iic)
      measurable_id.inv measurable_const
  apply (intervalIntegrable_const (c := a⁻¹)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  split_ifs with ht
  · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha.trans_le ht.1))]
    exact (inv_le_inv₀ (ha.trans_le ht.1) ha).mpr ht.1
  · simp only [norm_zero]
    exact (inv_pos.mpr ha).le

lemma reciprocal_middle_assembled_reciprocal_rectangle_integral (x a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ x) :
    (∫ t in (1 : ℝ)..x, if a ≤ t ∧ t ≤ b then t⁻¹ else 0) =
      Real.log (b / a) := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  let f : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then t⁻¹ else 0
  have hi (l r : ℝ) : IntervalIntegrable f volume l r :=
    reciprocal_middle_assembled_reciprocal_rectangle_intervalIntegrable a b l r hap
  have hleft : (∫ t in (1 : ℝ)..a, f t) = 0 := by
    calc
      _ = ∫ _ in (1 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha
        intro t ht
        exact if_neg (by intro h; linarith [ht.2, h.1])
      _ = 0 := by simp
  have hmid : (∫ t in a..b, f t) = Real.log (b / a) := by
    calc
      _ = ∫ t in a..b, t⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        exact if_pos ⟨ht.1.le, ht.2.le⟩
      _ = _ := integral_inv_of_pos hap hbp
  have hright : (∫ t in b..x, f t) = 0 := by
    calc
      _ = ∫ _ in b..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb
        intro t ht
        exact if_neg (by intro h; linarith [ht.1, h.2])
      _ = 0 := by simp
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals (hi 1 a) (hi a b)
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals (hi 1 b) (hi b x)
  rw [hleft, hmid, zero_add] at hsplit₁
  rw [← hsplit₁, hright, add_zero] at hsplit₂
  exact hsplit₂.symm

lemma reciprocal_middle_assembled_sum_Icc_floor_cutoff (c : ℕ → ℝ) (x t : ℝ) (ht : 0 ≤ t) (htx : t ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, if (d : ℝ) ≤ t then c d else 0) =
      ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d := by
  have hsub : Finset.Icc 1 ⌊t⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htx)
  have he := Finset.sum_subset hsub (f := fun (d : ℕ) => if (d : ℝ) ≤ t then c d else 0)
    (by
      intro d hd hdt
      have hnot : ¬ (d : ℝ) ≤ t := by
        intro h
        exact hdt (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          (Nat.le_floor_iff ht).mpr h⟩)
      exact if_neg hnot)
  rw [← he]
  apply Finset.sum_congr rfl
  intro d hd
  exact if_pos ((Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hd).2)

lemma reciprocal_middle_assembled_floor_div_as_finite_cutoffs (x t : ℝ) (hx : 1 ≤ x) (ht : 1 ≤ t) :
    (⌊x / t⌋₊ : ℝ) =
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if t ≤ x / (k : ℝ) then (1 : ℝ) else 0 := by
  have hxp : 0 < x := by linarith
  have htp : 0 < t := by linarith
  have hxt : x / t ≤ x := (div_le_iff₀ htp).mpr (by nlinarith)
  have he := reciprocal_middle_assembled_sum_Icc_floor_cutoff (fun _ => (1 : ℝ)) x (x / t)
    (div_nonneg hxp.le htp.le) hxt
  have hswap :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if (k : ℝ) ≤ x / t then (1 : ℝ) else 0) =
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if t ≤ x / (k : ℝ) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hiff : (k : ℝ) ≤ x / t ↔ t ≤ x / (k : ℝ) := by
      rw [le_div_iff₀ htp, le_div_iff₀ hkp, mul_comm (k : ℝ) t]
    simp only [hiff]
  rw [hswap] at he
  simpa using he.symm

lemma reciprocal_middle_assembled_moebius_floor_kernel_as_rectangles (x t : ℝ) (hx : 1 ≤ x)
    (ht : t ∈ Set.Icc 1 x) :
    (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
  rw [reciprocal_middle_assembled_floor_div_as_finite_cutoffs x t hx ht.1,
    ← reciprocal_middle_assembled_sum_Icc_floor_cutoff (fun d => ((moebius d : ℤ) : ℝ)) x t
      (by linarith [ht.1]) ht.2]
  rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp_all

lemma reciprocal_middle_assembled_moebius_floor_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x := by
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_middle_assembled_reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
  have hs : IntervalIntegrable (fun t : ℝ =>
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    convert IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊) (fun d hd =>
      IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊) (fun k _ => hterm d hd k)) using 1 <;>
      first | rfl | (funext t; simp only [Finset.sum_apply])
  apply hs.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  exact (reciprocal_middle_assembled_moebius_floor_kernel_as_rectangles x t hx ⟨ht.1.le, ht.2.le⟩).symm

theorem reciprocal_middle_assembled_moebius_logarithmic_floor_integral (x : ℝ) (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_middle_assembled_reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
  have hrow (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) :
      IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    convert IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊)
      (fun k _ => hterm d hd k) using 1 <;>
      first | rfl | (funext t; simp only [Finset.sum_apply])
  have heach (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊)
      (k : ℕ) (hk : k ∈ Finset.Icc 1 ⌊x⌋₊) :
      (∫ t in (1 : ℝ)..x, ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) =
        if k ≤ ⌊x⌋₊ / d then ((moebius d : ℤ) : ℝ) *
          Real.log (x / ((d * k : ℕ) : ℝ)) else 0 := by
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd1
    have hkp : (0 : ℝ) < k := by exact_mod_cast hk1
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rw [intervalIntegral.integral_const_mul]
    by_cases hkd : k ≤ ⌊x⌋₊ / d
    · rw [if_pos hkd]
      have hprod : d * k ≤ ⌊x⌋₊ := by
        calc
          _ ≤ d * (⌊x⌋₊ / d) := Nat.mul_le_mul_left d hkd
          _ ≤ ⌊x⌋₊ := by simpa only [mul_comm] using Nat.div_mul_le_self ⌊x⌋₊ d
      have hprodR : (d : ℝ) * k ≤ x := by
        have h := (Nat.le_floor_iff hx0).mp hprod
        simpa only [Nat.cast_mul] using h
      have hdxk : (d : ℝ) ≤ x / k := (le_div_iff₀ hkp).mpr hprodR
      have hxkx : x / (k : ℝ) ≤ x := (div_le_iff₀ hkp).mpr (by nlinarith)
      rw [reciprocal_middle_assembled_reciprocal_rectangle_integral x d (x / k) hdR hdxk hxkx]
      congr 2
      push_cast
      field_simp
    · rw [if_neg hkd]
      have hnot : ¬ (d : ℝ) ≤ x / k := by
        intro h
        have hprodR : (k : ℝ) * d ≤ x := by
          have hh := (le_div_iff₀ hkp).mp h
          nlinarith
        have hprodN : k * d ≤ ⌊x⌋₊ :=
          (Nat.le_floor_iff hx0).mpr (by simpa only [Nat.cast_mul] using hprodR)
        exact hkd ((Nat.le_div_iff_mul_le hd1).mpr hprodN)
      have hz : (fun t : ℝ => if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) =
          (fun _ : ℝ => (0 : ℝ)) := by
        funext t
        exact if_neg (fun h => hnot (h.1.trans h.2))
      rw [hz]
      simp
  calc
    _ = ∫ t in (1 : ℝ)..x,
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          ((moebius d : ℤ) : ℝ) *
            (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact reciprocal_middle_assembled_moebius_floor_kernel_as_rectangles x t hx ht
    _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ∫ t in (1 : ℝ)..x, ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
      rw [intervalIntegral.integral_finsetSum hrow]
      apply Finset.sum_congr rfl
      intro d hd
      exact intervalIntegral.integral_finsetSum (fun k _ => hterm d hd k)
    _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ / d),
        ((moebius d : ℤ) : ℝ) * Real.log (x / ((d * k : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_congr rfl (fun k hk => heach d hd k hk)]
      have hsub : Finset.Icc 1 (⌊x⌋₊ / d) ⊆ Finset.Icc 1 ⌊x⌋₊ :=
        Finset.Icc_subset_Icc le_rfl (Nat.div_le_self _ _)
      rw [← Finset.sum_subset hsub (f := fun k : ℕ =>
        if k ≤ ⌊x⌋₊ / d then ((moebius d : ℤ) : ℝ) *
          Real.log (x / ((d * k : ℕ) : ℝ)) else 0) (by
            intro k hk hnot
            exact if_neg (fun h => hnot (Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp hk).1, h⟩)))]
      apply Finset.sum_congr rfl
      intro k hk
      exact if_pos (Finset.mem_Icc.mp hk).2
    _ = Real.log x := reciprocal_middle_assembled_moebius_real_logarithmic_kernel_identity x hx

theorem reciprocal_middle_assembled_moebius_logarithmic_floor_integral_certificate (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x ∧
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  exact ⟨reciprocal_middle_assembled_moebius_floor_kernel_intervalIntegrable x hx, reciprocal_middle_assembled_moebius_logarithmic_floor_integral x hx⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_middle_assembled_sum_Icc_zero_remove (c : ℕ → ℝ) (hc : c 0 = 0) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d) = ∑ d ∈ Finset.Icc 1 N, c d := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [hc, zero_add]
  rfl

lemma reciprocal_middle_assembled_summatory_mul_continuous_intervalIntegrable (c : ℕ → ℝ) (f : ℝ → ℝ)
    (x : ℝ) (hx : 1 ≤ x) (hf : ContinuousOn f (Set.Icc 1 x)) :
    IntervalIntegrable (fun t : ℝ => f t * ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d)
      volume 1 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 1)
    (hf.integrableOn_Icc)

lemma reciprocal_middle_assembled_moebius_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hi := reciprocal_middle_assembled_summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => t⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

lemma reciprocal_middle_assembled_moebius_summatory_div_sq_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 1 x) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have hi := reciprocal_middle_assembled_summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => (t ^ 2)⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

theorem reciprocal_middle_assembled_moebius_reciprocal_abel_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        ∫ t in (1 : ℝ)..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) :=
    ((continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 1 x) := by
    simpa only [deriv_inv'] using hc.integrableOn_Icc
  have hmu0 : ((moebius 0 : ℤ) : ℝ) = 0 := by simp
  have h := sum_mul_eq_sub_integral_mul₀ (fun d => ((moebius d : ℤ) : ℝ))
    hmu0 x hd hi
  simp_rw [reciprocal_middle_assembled_sum_Icc_zero_remove (fun d => ((moebius d : ℤ) : ℝ)) hmu0] at h
  have hleft :
      (∑ d ∈ Finset.Icc 0 ⌊x⌋₊, (d : ℝ)⁻¹ * ((moebius d : ℤ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [reciprocal_middle_assembled_sum_Icc_zero_remove _ (by simp)]
    apply Finset.sum_congr rfl
    intro d _
    simp only [div_eq_mul_inv, mul_comm]
  rw [hleft] at h
  have hneg :
      (∫ t in Set.Ioc (1 : ℝ) x,
        deriv (fun t : ℝ => t⁻¹) t * ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) =
        -(∫ t in (1 : ℝ)..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    simp_rw [deriv_inv, neg_mul, mul_comm ((_)⁻¹), ← div_eq_mul_inv]
    exact intervalIntegral.integral_neg
  rw [hneg] at h
  simpa only [div_eq_mul_inv, mul_comm, sub_neg_eq_add] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_middle_assembled_moebius_fractional_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (x / t - (⌊x / t⌋₊ : ℝ)) *
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hi := ((reciprocal_middle_assembled_moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x).sub
    (reciprocal_middle_assembled_moebius_floor_kernel_intervalIntegrable x hx)
  apply hi.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htne : t ≠ 0 := by linarith [ht.1]
  dsimp only
  field_simp [htne]

theorem reciprocal_middle_assembled_moebius_reciprocal_fractional_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        (∫ t in (1 : ℝ)..x, (x / t - (⌊x / t⌋₊ : ℝ)) *
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) / x +
        Real.log x / x := by
  have hxne : x ≠ 0 := by linarith
  have he :
      (∫ t in (1 : ℝ)..x, (x / t - (⌊x / t⌋₊ : ℝ)) *
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      x * (∫ t in (1 : ℝ)..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) - Real.log x := by
    calc
      _ = ∫ t in (1 : ℝ)..x,
          x * ((∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) -
            (⌊x / t⌋₊ : ℝ) *
              (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have htne : t ≠ 0 := by linarith [ht.1]
        field_simp [htne]
      _ = _ := by
        rw [intervalIntegral.integral_sub
          ((reciprocal_middle_assembled_moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x)
          (reciprocal_middle_assembled_moebius_floor_kernel_intervalIntegrable x hx),
          intervalIntegral.integral_const_mul, reciprocal_middle_assembled_moebius_logarithmic_floor_integral x hx]
  rw [reciprocal_middle_assembled_moebius_reciprocal_abel_identity x hx, he]
  field_simp
  ring

lemma reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) volume 1 x := by
  apply (reciprocal_middle_assembled_moebius_summatory_div_intervalIntegrable x hx).abs.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htp : 0 < t := by linarith [ht.1]
  exact abs_div _ t |>.trans (by rw [abs_of_pos htp])

theorem reciprocal_middle_assembled_moebius_reciprocal_el_marraki_bound (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        (∫ t in (1 : ℝ)..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) / x +
        Real.log x / x := by
  have hxp : 0 < x := by linarith
  let R : ℝ → ℝ := fun t => (x / t - (⌊x / t⌋₊ : ℝ)) *
    (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t
  have hiR : IntervalIntegrable R volume 1 x :=
    reciprocal_middle_assembled_moebius_fractional_kernel_intervalIntegrable x hx
  have hiB := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable x hx
  have hrem : |∫ t in (1 : ℝ)..x, R t| ≤
      ∫ t in (1 : ℝ)..x, |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t := by
    apply (intervalIntegral.abs_integral_le_integral_abs hx).trans
    apply intervalIntegral.integral_mono_on hx hiR.abs hiB
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hyt : 0 ≤ x / t := div_nonneg hxp.le htp.le
    have hlo : 0 ≤ x / t - (⌊x / t⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hyt)
    have hup : x / t - (⌊x / t⌋₊ : ℝ) ≤ 1 := by
      have hh := Nat.lt_floor_add_one (x / t)
      linarith
    dsimp only [R]
    rw [abs_div, abs_mul, abs_of_nonneg hlo, abs_of_pos htp]
    apply div_le_div_of_nonneg_right _ htp.le
    calc
      _ ≤ 1 * |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_right hup (abs_nonneg _)
      _ = _ := one_mul _
  have hid := reciprocal_middle_assembled_moebius_reciprocal_fractional_identity x hx
  change (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
      (∫ t in (1 : ℝ)..x, R t) / x + Real.log x / x at hid
  rw [hid]
  calc
    _ ≤ |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        (∫ t in (1 : ℝ)..x, R t) / x| + |Real.log x / x| := abs_add_le _ _
    _ ≤ (|(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x| +
        |(∫ t in (1 : ℝ)..x, R t) / x|) + |Real.log x / x| :=
      by
        have hh := abs_add_le
          ((∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x)
          ((∫ t in (1 : ℝ)..x, R t) / x)
        linarith
    _ = |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        |∫ t in (1 : ℝ)..x, R t| / x + Real.log x / x := by
      rw [abs_div, abs_div, abs_div, abs_of_pos hxp,
        abs_of_nonneg (Real.log_nonneg hx)]
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hrem hxp.le
      linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_middle_assembled_hasDerivAt_scaled_id_div_log (A t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => A * t / Real.log t)
      ((A * Real.log t - A) / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((hasDerivAt_id t).const_mul A).div (Real.hasDerivAt_log ht0) hl0
  convert hd using 1 <;> first | rfl | (dsimp only [id]; field_simp [ht0])

lemma reciprocal_middle_assembled_scaled_log_primitive_integral (A a x : ℝ) (ha : 1 < a) (hax : a ≤ x) :
    (∫ t in a..x, (A * Real.log t - A) / Real.log t ^ 2) =
      A * x / Real.log x - A * a / Real.log a := by
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hi : IntervalIntegrable (fun t : ℝ => (A * Real.log t - A) / Real.log t ^ 2)
      volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro t ht
  rw [Set.uIcc_of_le hax] at ht
  exact reciprocal_middle_assembled_hasDerivAt_scaled_id_div_log A t (lt_of_lt_of_le ha ht.1)

theorem reciprocal_middle_assembled_moebius_reciprocal_decay_transfer (a x A B C : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hBA : A ≤ B)
    (hM : ∀ t ∈ Set.Icc a x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        (A * Real.log t - B) * t / Real.log t ^ 2)
    (hinitial : (∫ t in (1 : ℝ)..a,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ C) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (2 * A * Real.log x - B) / Real.log x ^ 2 +
        (C - A * a / Real.log a + Real.log x) / x := by
  have hx : 1 ≤ x := (le_of_lt ha).trans hax
  have hxp : 0 < x := by linarith
  have hxl : Real.log x ≠ 0 := (Real.log_pos (lt_of_lt_of_le ha hax)).ne'
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)
  have hi1a := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable a ha.le
  have hi1x := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable x hx
  have hiax : IntervalIntegrable (fun t : ℝ => |M t| / t) volume a x :=
    hi1a.symm.trans hi1x
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hiP : IntervalIntegrable (fun t : ℝ => (A * Real.log t - A) / Real.log t ^ 2)
      volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  have hiupper : (∫ t in a..x, |M t| / t) ≤
      A * x / Real.log x - A * a / Real.log a := by
    rw [← reciprocal_middle_assembled_scaled_log_primitive_integral A a x ha hax]
    apply intervalIntegral.integral_mono_on hax hiax hiP
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    calc
      |M t| / t ≤ ((A * Real.log t - B) * t / Real.log t ^ 2) / t :=
        div_le_div_of_nonneg_right (hM t ht) htp.le
      _ = (A * Real.log t - B) / Real.log t ^ 2 := by
        field_simp
      _ ≤ (A * Real.log t - A) / Real.log t ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hitotal : (∫ t in (1 : ℝ)..x, |M t| / t) ≤
      C + A * x / Real.log x - A * a / Real.log a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1a hiax]
    change (∫ t in (1 : ℝ)..a, |M t| / t) ≤ C at hinitial
    linarith
  have hxM : |M x| / x ≤ (A * Real.log x - B) / Real.log x ^ 2 := by
    calc
      _ ≤ ((A * Real.log x - B) * x / Real.log x ^ 2) / x :=
        div_le_div_of_nonneg_right (hM x ⟨hax, le_rfl⟩) hxp.le
      _ = _ := by field_simp
  have hi := div_le_div_of_nonneg_right hitotal hxp.le
  have hel := reciprocal_middle_assembled_moebius_reciprocal_el_marraki_bound x hx
  change |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
    |M x| / x + (∫ t in (1 : ℝ)..x, |M t| / t) / x + Real.log x / x at hel
  have halg :
      (A * Real.log x - B) / Real.log x ^ 2 +
        (C + A * x / Real.log x - A * a / Real.log a) / x + Real.log x / x =
      (2 * A * Real.log x - B) / Real.log x ^ 2 +
        (C - A * a / Real.log a + Real.log x) / x := by
    field_simp
    ring
  rw [← halg]
  linarith

lemma reciprocal_middle_assembled_logarithmic_initial_error_bound (x : ℝ) (hx : 1200000 ≤ x) :
    (303 + Real.log x) / x ≤ (4 / 1000) / Real.log x := by
  let T : ℝ := 1200000
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hxe : Real.exp 2 ≤ T := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith
  have hTe : Real.exp 1 ≤ T := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hxe
  have hTx : T ≤ x := hx
  have hlogT : Real.log T ≤ 15 := by
    apply (Real.log_le_iff_le_exp hTpos).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : T ≤ ∑ i ∈ Finset.range 15, (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [T, Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hlin : Real.log x / x ≤ Real.log T / T :=
    Real.log_div_self_antitoneOn hTe (hTe.trans hTx) hTx
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hsq := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hsq
  have hlogT2 : Real.log T ^ 2 ≤ 15 ^ 2 :=
    pow_le_pow_left₀ hlogT0 hlogT 2
  have hbound : 303 * (Real.log x / x) + Real.log x ^ 2 / x ≤ 4 / 1000 := by
    calc
      _ ≤ 303 * (Real.log T / T) + Real.log T ^ 2 / T := by
        have h1 := mul_le_mul_of_nonneg_left hlin (by norm_num : (0 : ℝ) ≤ 303)
        linarith
      _ ≤ 303 * (15 / T) + 15 ^ 2 / T := by
        have h1 := div_le_div_of_nonneg_right hlogT hTpos.le
        have h2 := div_le_div_of_nonneg_right hlogT2 hTpos.le
        linarith
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ hlogxp).mpr
  convert hbound using 1 <;> first | rfl | ring

theorem reciprocal_middle_assembled_moebius_reciprocal_point_zero_three_of_summatory_bound (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        ((13 / 1000) * Real.log t - 118 / 1000) * t / Real.log t ^ 2)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hxa : (1078853 : ℝ) ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga : 0 < Real.log (1078853 : ℝ) := Real.log_pos (by norm_num)
  have h := reciprocal_middle_assembled_moebius_reciprocal_decay_transfer 1078853 x (13 / 1000) (118 / 1000) 303
    (by norm_num) hxa (by norm_num) hM hinitial
  have hmain : (2 * (13 / 1000) * Real.log x - 118 / 1000) / Real.log x ^ 2 ≤
      (26 / 1000) / Real.log x := by
    calc
      _ ≤ ((26 / 1000) * Real.log x) / Real.log x ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  have hinit : (303 - (13 / 1000) * 1078853 / Real.log (1078853 : ℝ) + Real.log x) / x ≤
      (303 + Real.log x) / x := by
    apply div_le_div_of_nonneg_right _ hxp.le
    have hp : (0 : ℝ) ≤ (13 / 1000) * 1078853 / Real.log (1078853 : ℝ) :=
      div_nonneg (by norm_num) hloga.le
    linarith
  have herr := reciprocal_middle_assembled_logarithmic_initial_error_bound x hx
  have heq : (26 / 1000) / Real.log x + (4 / 1000) / Real.log x =
      (3 / 100) / Real.log x := by ring
  rw [← heq]
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem reciprocal_middle_assembled_moebius_reciprocal_log_rate_transfer (a x A c C : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hlog : c ≤ (c - 1) * Real.log a)
    (hM : ∀ t ∈ Set.Icc a x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤ A * t / Real.log t)
    (hinitial : (∫ t in (1 : ℝ)..a,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ C) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (1 + c) * A / Real.log x +
        (C - c * A * a / Real.log a + Real.log x) / x := by
  have hx : 1 ≤ x := ha.le.trans hax
  have hxp : 0 < x := by linarith
  have hxl : Real.log x ≠ 0 := (Real.log_pos (ha.trans_le hax)).ne'
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)
  have hi1a := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable a ha.le
  have hi1x := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable x hx
  have hiax : IntervalIntegrable (fun t : ℝ => |M t| / t) volume a x :=
    hi1a.symm.trans hi1x
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht
    exact (Real.log_pos (ha.trans_le ht.1)).ne'
  have hiP : IntervalIntegrable
      (fun t : ℝ => (c * A * Real.log t - c * A) / Real.log t ^ 2) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  have hiupper : (∫ t in a..x, |M t| / t) ≤
      c * A * x / Real.log x - c * A * a / Real.log a := by
    rw [← reciprocal_middle_assembled_scaled_log_primitive_integral (c * A) a x ha hax]
    apply intervalIntegral.integral_mono_on hax hiax hiP
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have htl := Real.log_pos (ha.trans_le ht.1)
    have hlogt : c ≤ (c - 1) * Real.log t := by
      have hla : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
      have hm := mul_le_mul_of_nonneg_left hla (by linarith : 0 ≤ c - 1)
      linarith
    calc
      |M t| / t ≤ (A * t / Real.log t) / t :=
        div_le_div_of_nonneg_right (hM t ht) htp.le
      _ = A / Real.log t := by field_simp
      _ ≤ (c * A * Real.log t - c * A) / Real.log t ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos htl)).mpr
        have heq : A / Real.log t * Real.log t ^ 2 = A * Real.log t := by
          field_simp
        rw [heq]
        nlinarith [mul_nonneg hA (sub_nonneg.mpr hlogt)]
  have hitotal : (∫ t in (1 : ℝ)..x, |M t| / t) ≤
      C + c * A * x / Real.log x - c * A * a / Real.log a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1a hiax]
    change (∫ t in (1 : ℝ)..a, |M t| / t) ≤ C at hinitial
    linarith
  have hxM : |M x| / x ≤ A / Real.log x := by
    calc
      _ ≤ (A * x / Real.log x) / x :=
        div_le_div_of_nonneg_right (hM x ⟨hax, le_rfl⟩) hxp.le
      _ = _ := by field_simp
  have hi := div_le_div_of_nonneg_right hitotal hxp.le
  have hel := reciprocal_middle_assembled_moebius_reciprocal_el_marraki_bound x hx
  change |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
    |M x| / x + (∫ t in (1 : ℝ)..x, |M t| / t) / x + Real.log x / x at hel
  have halg : A / Real.log x +
      (C + c * A * x / Real.log x - c * A * a / Real.log a) / x +
      Real.log x / x = (1 + c) * A / Real.log x +
      (C - c * A * a / Real.log a + Real.log x) / x := by
    field_simp
    ring
  rw [← halg]
  linarith

lemma reciprocal_middle_assembled_logarithmic_square_tail_bound (x : ℝ) (hx : 1200000 ≤ x) :
    Real.log x / x ≤ (1 / 5000) / Real.log x := by
  let T : ℝ := 1200000
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hxe : Real.exp 2 ≤ T := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith
  have hTx : T ≤ x := hx
  have hlogT : Real.log T ≤ 15 := by
    apply (Real.log_le_iff_le_exp hTpos).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : T ≤ ∑ i ∈ Finset.range 15, (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [T, Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hsq := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hsq
  have hlogT2 : Real.log T ^ 2 ≤ 15 ^ 2 := pow_le_pow_left₀ hlogT0 hlogT 2
  have hbound : Real.log x ^ 2 / x ≤ 1 / 5000 := by
    calc
      _ ≤ Real.log T ^ 2 / T := hsquare
      _ ≤ 15 ^ 2 / T := div_le_div_of_nonneg_right hlogT2 hTpos.le
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ hlogxp).mpr
  convert hbound using 1 <;> first | rfl | ring

theorem reciprocal_middle_assembled_moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        (7 / 500) * t / Real.log t)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hxa : (1078853 : ℝ) ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga : 0 < Real.log (1078853 : ℝ) := Real.log_pos (by norm_num)
  have hloglo : (27 / 2 : ℝ) ≤ Real.log (1078853 : ℝ) := by
    have h10 : (23 / 10 : ℝ) ≤ Real.log 10 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hmillion : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
      rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 1000000)
      (by norm_num : (1000000 : ℝ) ≤ 1078853)
    rw [hmillion] at hm
    linarith
  have hloghi : Real.log (1078853 : ℝ) ≤ 15 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : (1078853 : ℝ) ≤ ∑ i ∈ Finset.range 15,
        (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have h := reciprocal_middle_assembled_moebius_reciprocal_log_rate_transfer 1078853 x (7 / 500) (27 / 25) 303
    (by norm_num) hxa (by norm_num) (by norm_num) (by nlinarith) hM hinitial
  have hoffset : (303 : ℝ) ≤ (27 / 25) * (7 / 500) * 1078853 /
      Real.log (1078853 : ℝ) := by
    apply (le_div_iff₀ hloga).mpr
    nlinarith
  have herr : (303 - (27 / 25) * (7 / 500) * 1078853 /
      Real.log (1078853 : ℝ) + Real.log x) / x ≤ Real.log x / x :=
    div_le_div_of_nonneg_right (by linarith) hxp.le
  have htail := reciprocal_middle_assembled_logarithmic_square_tail_bound x hx
  have hmain : (1 + (27 / 25 : ℝ)) * (7 / 500) / Real.log x +
      (1 / 5000) / Real.log x ≤ (3 / 100) / Real.log x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hlogxp.le
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

noncomputable def reciprocal_middle_assembled_reciprocalMiddleM (t : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)

lemma reciprocal_middle_assembled_reciprocal_middle_log_ten :
    (23 / 10 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2303 / 1000 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma reciprocal_middle_assembled_reciprocal_middle_real_hurst
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (t : ℝ) (hlo : 80000 ≤ t) (hhi : t ≤ 10 ^ 16) :
    |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ (571 / 1000 : ℝ) * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have hklo : 80000 ≤ ⌊t⌋₊ := Nat.le_floor hlo
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hkhi : ⌊t⌋₊ ≤ 10 ^ 16 := by
    exact_mod_cast hfloor.trans hhi
  exact (hHurst ⌊t⌋₊ hklo hkhi).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfloor) (by norm_num))

lemma reciprocal_middle_assembled_reciprocal_middle_real_tail
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (t : ℝ) (ht : 10 ^ 16 ≤ t) :
    |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ t / 4345 := by
  have ht0 : 0 ≤ t := by linarith
  have hklo : 10 ^ 16 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  exact (hTail ⌊t⌋₊ hklo).trans
    (div_le_div_of_nonneg_right (Nat.floor_le ht0) (by norm_num))

lemma reciprocal_middle_assembled_reciprocal_middle_hurst_log_bound
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (t : ℝ) (hlo : 1000000 ≤ t) (hhi : t ≤ 10 ^ 16) :
    |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ (7 / 500) * t / Real.log t := by
  have htp : 0 < t := by linarith
  have hlogp : 0 < Real.log t := Real.log_pos (by linarith)
  have hsqrtp : 0 < Real.sqrt t := Real.sqrt_pos.2 htp
  have hexp : Real.exp 2 ≤ (1000000 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlogmillion : Real.log (1000000 : ℝ) ≤ 15 := by
    rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [reciprocal_middle_assembled_reciprocal_middle_log_ten.2]
  have hlogsqrt : Real.log t / Real.sqrt t ≤ (15 / 1000 : ℝ) := by
    calc
      _ ≤ Real.log (1000000 : ℝ) / Real.sqrt 1000000 :=
        Real.log_div_sqrt_antitoneOn hexp (hexp.trans hlo) hlo
      _ ≤ _ := by norm_num; linarith
  have hlog : Real.log t ≤ (15 / 1000 : ℝ) * Real.sqrt t :=
    (div_le_iff₀ hsqrtp).mp hlogsqrt
  have hM := reciprocal_middle_assembled_reciprocal_middle_real_hurst hHurst t (by linarith) hhi
  apply (le_div_iff₀ hlogp).mpr
  calc
    |reciprocal_middle_assembled_reciprocalMiddleM t| * Real.log t
        ≤ ((571 / 1000 : ℝ) * Real.sqrt t) * Real.log t :=
      mul_le_mul_of_nonneg_right hM hlogp.le
    _ ≤ ((571 / 1000 : ℝ) * Real.sqrt t) *
        ((15 / 1000 : ℝ) * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (8565 / 1000000 : ℝ) * t := by
      nlinarith [Real.sq_sqrt htp.le]
    _ ≤ _ := by nlinarith

lemma reciprocal_middle_assembled_reciprocal_middle_tail_log_bound
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (t A L : ℝ) (ht : 10 ^ 16 ≤ t) (_hA : 0 ≤ A)
    (hlog : Real.log t ≤ L) (hscalar : L ≤ A * 4345) :
    |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ A * t / Real.log t := by
  have htp : 0 < t := by linarith
  have hlp : 0 < Real.log t := Real.log_pos (by linarith)
  apply (le_div_iff₀ hlp).mpr
  have hM := reciprocal_middle_assembled_reciprocal_middle_real_tail hTail t ht
  calc
    |reciprocal_middle_assembled_reciprocalMiddleM t| * Real.log t ≤ (t / 4345) * Real.log t :=
      mul_le_mul_of_nonneg_right hM hlp.le
    _ ≤ (t / 4345) * (A * 4345) :=
      mul_le_mul_of_nonneg_left (hlog.trans hscalar) (by positivity)
    _ = A * t := by ring

theorem reciprocal_middle_assembled_moebius_reciprocal_middle_first_of_hurst_and_tail
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303)
    (x : ℝ) (hx : 1200000 ≤ x) (hhi : x ≤ 10 ^ 24) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  apply reciprocal_middle_assembled_moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound x hx _ hinitial
  intro t ht
  change |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ _
  by_cases ht16 : t ≤ 10 ^ 16
  · exact reciprocal_middle_assembled_reciprocal_middle_hurst_log_bound hHurst t (by linarith [ht.1]) ht16
  · apply reciprocal_middle_assembled_reciprocal_middle_tail_log_bound hTail t (7 / 500) (24 * (2303 / 1000))
      (le_of_not_ge ht16) (by norm_num) _ (by norm_num)
    have hlog := Real.log_le_log (by linarith [ht.1] : 0 < t) (ht.2.trans hhi)
    rw [Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith [reciprocal_middle_assembled_reciprocal_middle_log_ten.2]

lemma reciprocal_middle_assembled_reciprocal_middle_hurst_div
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (t r : ℝ) (hlo : 80000 ≤ t) (hhi : t ≤ 10 ^ 16)
    (hr : 0 < r) (hrt : r ^ 2 ≤ t) :
    |reciprocal_middle_assembled_reciprocalMiddleM t| / t ≤ (571 / 1000) / r := by
  have htp : 0 < t := by linarith
  have hsqrtp : 0 < Real.sqrt t := Real.sqrt_pos.2 htp
  have hroot : r ≤ Real.sqrt t := (Real.le_sqrt hr.le htp.le).2 hrt
  calc
    _ ≤ ((571 / 1000 : ℝ) * Real.sqrt t) / t :=
      div_le_div_of_nonneg_right (reciprocal_middle_assembled_reciprocal_middle_real_hurst hHurst t hlo hhi) htp.le
    _ = (571 / 1000) / Real.sqrt t := by
      apply (div_eq_div_iff htp.ne' hsqrtp.ne').2
      nlinarith [Real.sq_sqrt htp.le]
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hr hroot

lemma reciprocal_middle_assembled_reciprocal_middle_hurst_integral
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (l u r : ℝ) (hlo : 80000 ≤ l) (hlu : l ≤ u)
    (hhi : u ≤ 10 ^ 16) (hr : 0 < r) (hrl : r ^ 2 ≤ l) :
    (∫ t in l..u, |reciprocal_middle_assembled_reciprocalMiddleM t| / t) ≤
      (u - l) * ((571 / 1000) / r) := by
  have hil := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable l (by linarith)
  have hiu := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable u (by linarith)
  calc
    _ ≤ ∫ _t in l..u, ((571 / 1000 : ℝ) / r) := by
      apply intervalIntegral.integral_mono_on hlu (hil.symm.trans hiu) intervalIntegrable_const
      intro t ht
      exact reciprocal_middle_assembled_reciprocal_middle_hurst_div hHurst t r (hlo.trans ht.1)
        (ht.2.trans hhi) hr (hrl.trans ht.1)
    _ = _ := by simp; ring

lemma reciprocal_middle_assembled_reciprocal_middle_tail_integral
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (a : ℝ) (ha : 10 ^ 16 ≤ a) :
    (∫ t in (10 ^ 16 : ℝ)..a, |reciprocal_middle_assembled_reciprocalMiddleM t| / t) ≤
      (a - 10 ^ 16) / 4345 := by
  have hil := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable (10 ^ 16) (by norm_num)
  have hiu := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable a (by linarith)
  calc
    _ ≤ ∫ _t in (10 ^ 16 : ℝ)..a, (1 / 4345 : ℝ) := by
      apply intervalIntegral.integral_mono_on ha (hil.symm.trans hiu) intervalIntegrable_const
      intro t ht
      have htp : 0 < t := by linarith [ht.1]
      have hM := reciprocal_middle_assembled_reciprocal_middle_real_tail hTail t ht.1
      apply (div_le_iff₀ htp).mpr
      convert hM using 1 <;> first | rfl | ring
    _ = _ := by simp [div_eq_mul_inv]

lemma reciprocal_middle_assembled_reciprocal_middle_initial_at_large_anchor
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    (∫ t in (1 : ℝ)..(10 ^ 24 : ℝ),
      |reciprocal_middle_assembled_reciprocalMiddleM t| / t) ≤ (10 ^ 24 : ℝ) / 4345 := by
  have hi1 := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable 1078853 (by norm_num)
  have hiB := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable (10 ^ 8) (by norm_num)
  have hiT := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable (10 ^ 16) (by norm_num)
  have hia := reciprocal_middle_assembled_moebius_abs_summatory_div_intervalIntegrable (10 ^ 24) (by norm_num)
  change IntervalIntegrable (fun t => |reciprocal_middle_assembled_reciprocalMiddleM t| / t) volume 1 1078853 at hi1
  change IntervalIntegrable (fun t => |reciprocal_middle_assembled_reciprocalMiddleM t| / t) volume 1 (10 ^ 8) at hiB
  change IntervalIntegrable (fun t => |reciprocal_middle_assembled_reciprocalMiddleM t| / t) volume 1 (10 ^ 16) at hiT
  change IntervalIntegrable (fun t => |reciprocal_middle_assembled_reciprocalMiddleM t| / t) volume 1 (10 ^ 24) at hia
  have hfirst := reciprocal_middle_assembled_reciprocal_middle_hurst_integral hHurst 1078853 (10 ^ 8) 1000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsecond := reciprocal_middle_assembled_reciprocal_middle_hurst_integral hHurst (10 ^ 8) (10 ^ 16) 10000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlast := reciprocal_middle_assembled_reciprocal_middle_tail_integral hTail (10 ^ 24) (by norm_num)
  change (∫ t in (1 : ℝ)..1078853, |reciprocal_middle_assembled_reciprocalMiddleM t| / t) ≤ 303 at hinitial
  rw [← intervalIntegral.integral_add_adjacent_intervals hiT (hiT.symm.trans hia),
    ← intervalIntegral.integral_add_adjacent_intervals hiB (hiB.symm.trans hiT),
    ← intervalIntegral.integral_add_adjacent_intervals hi1 (hi1.symm.trans hiB)]
  norm_num at hfirst hsecond hlast ⊢
  linarith

lemma reciprocal_middle_assembled_reciprocal_middle_sharp_log_square_tail (x : ℝ) (hx : 10 ^ 24 ≤ x) :
    Real.log x / x ≤ (1 / 100000) / Real.log x := by
  let T : ℝ := 10 ^ 8
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hxe : Real.exp 2 ≤ T := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hTx : T ≤ x := by dsimp only [T]; linarith
  have hlogT : Real.log T ≤ 20 := by
    dsimp only [T]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [reciprocal_middle_assembled_reciprocal_middle_log_ten.2]
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hsq := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hsq
  have hlogT2 : Real.log T ^ 2 ≤ 20 ^ 2 := pow_le_pow_left₀ hlogT0 hlogT 2
  have hbound : Real.log x ^ 2 / x ≤ 1 / 100000 := by
    calc
      _ ≤ Real.log T ^ 2 / T := hsquare
      _ ≤ 20 ^ 2 / T := div_le_div_of_nonneg_right hlogT2 hTpos.le
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ hlogxp).mpr
  convert hbound using 1 <;> first | rfl | ring

theorem reciprocal_middle_assembled_moebius_reciprocal_middle_second_of_hurst_and_tail
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303)
    (x : ℝ) (hx : 10 ^ 24 ≤ x) (hhi : x ≤ 10 ^ 28) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hloganchor : (552 / 10 : ℝ) ≤ Real.log (10 ^ 24 : ℝ) ∧
      Real.log (10 ^ 24 : ℝ) ≤ 60 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    constructor <;> nlinarith [reciprocal_middle_assembled_reciprocal_middle_log_ten.1, reciprocal_middle_assembled_reciprocal_middle_log_ten.2]
  have hM : ∀ t ∈ Set.Icc (10 ^ 24 : ℝ) x,
      |reciprocal_middle_assembled_reciprocalMiddleM t| ≤ (297 / 20000) * t / Real.log t := by
    intro t ht
    apply reciprocal_middle_assembled_reciprocal_middle_tail_log_bound hTail t (297 / 20000)
      (28 * (2303 / 1000)) (by linarith [ht.1]) (by norm_num) _ (by norm_num)
    have hlog := Real.log_le_log (by linarith [ht.1] : 0 < t) (ht.2.trans hhi)
    rw [Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith [reciprocal_middle_assembled_reciprocal_middle_log_ten.2]
  have h := reciprocal_middle_assembled_moebius_reciprocal_log_rate_transfer (10 ^ 24) x (297 / 20000)
    (1019 / 1000) ((10 ^ 24) / 4345) (by norm_num) hx (by norm_num)
    (by norm_num) (by nlinarith [hloganchor.1]) hM
    (reciprocal_middle_assembled_reciprocal_middle_initial_at_large_anchor hHurst hTail hinitial)
  have hlogap : 0 < Real.log (10 ^ 24 : ℝ) := Real.log_pos (by norm_num)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hxp : 0 < x := by linarith
  have hoffset : (10 ^ 24 : ℝ) / 4345 ≤
      (1019 / 1000) * (297 / 20000) * (10 ^ 24) / Real.log (10 ^ 24 : ℝ) := by
    apply (le_div_iff₀ hlogap).mpr
    norm_num at hloganchor ⊢
    nlinarith [hloganchor.2]
  have herr : ((10 ^ 24 : ℝ) / 4345 -
      (1019 / 1000) * (297 / 20000) * (10 ^ 24) / Real.log (10 ^ 24 : ℝ) +
      Real.log x) / x ≤ Real.log x / x :=
    div_le_div_of_nonneg_right (by linarith) hxp.le
  have htail := reciprocal_middle_assembled_reciprocal_middle_sharp_log_square_tail x hx
  have hmain : (1 + (1019 / 1000 : ℝ)) * (297 / 20000) / Real.log x +
      (1 / 100000) / Real.log x ≤ (3 / 100) / Real.log x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hlogxp.le
  linarith

theorem reciprocal_middle_assembled_moebius_reciprocal_middle_of_hurst_and_tail
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303)
    (x : ℝ) (hx : 1200000 ≤ x) (hhi : x ≤ 10 ^ 28) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  by_cases hx24 : x ≤ 10 ^ 24
  · exact reciprocal_middle_assembled_moebius_reciprocal_middle_first_of_hurst_and_tail hHurst hTail hinitial x hx hx24
  · exact reciprocal_middle_assembled_moebius_reciprocal_middle_second_of_hurst_and_tail hHurst hTail hinitial x
      (le_of_not_ge hx24) hhi

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail_complete
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (x : ℝ) (hx : 1200000 ≤ x) (hhi : x ≤ 10 ^ 28) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x :=
  reciprocal_middle_assembled_moebius_reciprocal_middle_of_hurst_and_tail hHurst hTail
    moebius_initial_integral_le_303 x hx hhi

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution 
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (x : ℝ) (hx : 1200000 ≤ x) (hhi : x ≤ 10 ^ 28) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := Helfgott.moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail_complete hHurst hTail x hx hhi
#print axioms solution
