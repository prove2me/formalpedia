-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_el_marraki_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T19:26:45.432994+00:00
-- url     : https://prove2.me/submissions/4c341bba-f2d7-47f2-ab1b-55d9305b6115

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
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

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
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

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
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
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]

lemma coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
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
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast coprime_moebius_divisor_expansion q n hq
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
    exact_mod_cast moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem moebius_real_logarithmic_kernel_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d∈Finset.Icc 1 (Nat.floor x),∑ k∈Finset.Icc 1 ((Nat.floor x)/d),
      ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x := by
  let N := Nat.floor x
  have hN : 1 ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  change (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
    ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x
  have hr := finite_positive_divisor_reindex N
    (fun d k => ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ)))
  have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (∑ d∈n.divisors,((moebius d : ℤ) : ℝ)*Real.log (x/((d*(n/d) : ℕ) : ℝ))) =
        (if n=1 then (1:ℝ) else 0)*Real.log (x/(n : ℝ)) := by
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1;omega
    have hemul : ∀ d∈n.divisors,d*(n/d)=n := fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [Finset.sum_congr rfl (fun d hd => by rw [hemul d hd]),←Finset.sum_mul]
    have hm : (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then 1 else 0 := by
      exact_mod_cast moebius_divisor_sum n hn0
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

lemma reciprocal_rectangle_intervalIntegrable (a b l r : ℝ) (ha : 0 < a) :
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

lemma reciprocal_rectangle_integral (x a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ x) :
    (∫ t in (1 : ℝ)..x, if a ≤ t ∧ t ≤ b then t⁻¹ else 0) =
      Real.log (b / a) := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  let f : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then t⁻¹ else 0
  have hi (l r : ℝ) : IntervalIntegrable f volume l r :=
    reciprocal_rectangle_intervalIntegrable a b l r hap
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

lemma sum_Icc_floor_cutoff (c : ℕ → ℝ) (x t : ℝ) (ht : 0 ≤ t) (htx : t ≤ x) :
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

lemma floor_div_as_finite_cutoffs (x t : ℝ) (hx : 1 ≤ x) (ht : 1 ≤ t) :
    (⌊x / t⌋₊ : ℝ) =
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if t ≤ x / (k : ℝ) then (1 : ℝ) else 0 := by
  have hxp : 0 < x := by linarith
  have htp : 0 < t := by linarith
  have hxt : x / t ≤ x := (div_le_iff₀ htp).mpr (by nlinarith)
  have he := sum_Icc_floor_cutoff (fun _ => (1 : ℝ)) x (x / t)
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

lemma moebius_floor_kernel_as_rectangles (x t : ℝ) (hx : 1 ≤ x)
    (ht : t ∈ Set.Icc 1 x) :
    (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
  rw [floor_div_as_finite_cutoffs x t hx ht.1,
    ← sum_Icc_floor_cutoff (fun d => ((moebius d : ℤ) : ℝ)) x t
      (by linarith [ht.1]) ht.2]
  rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp_all

lemma moebius_floor_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x := by
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
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
  exact (moebius_floor_kernel_as_rectangles x t hx ⟨ht.1.le, ht.2.le⟩).symm

theorem moebius_logarithmic_floor_integral (x : ℝ) (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
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
      rw [reciprocal_rectangle_integral x d (x / k) hdR hdxk hxkx]
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
      exact moebius_floor_kernel_as_rectangles x t hx ht
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
    _ = Real.log x := moebius_real_logarithmic_kernel_identity x hx

theorem moebius_logarithmic_floor_integral_certificate (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x ∧
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  exact ⟨moebius_floor_kernel_intervalIntegrable x hx, moebius_logarithmic_floor_integral x hx⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma sum_Icc_zero_remove (c : ℕ → ℝ) (hc : c 0 = 0) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d) = ∑ d ∈ Finset.Icc 1 N, c d := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [hc, zero_add]
  rfl

lemma summatory_mul_continuous_intervalIntegrable (c : ℕ → ℝ) (f : ℝ → ℝ)
    (x : ℝ) (hx : 1 ≤ x) (hf : ContinuousOn f (Set.Icc 1 x)) :
    IntervalIntegrable (fun t : ℝ => f t * ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d)
      volume 1 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 1)
    (hf.integrableOn_Icc)

lemma moebius_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hi := summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => t⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

lemma moebius_summatory_div_sq_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 1 x) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have hi := summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => (t ^ 2)⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

theorem moebius_reciprocal_abel_identity (x : ℝ) (hx : 1 ≤ x) :
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
  simp_rw [sum_Icc_zero_remove (fun d => ((moebius d : ℤ) : ℝ)) hmu0] at h
  have hleft :
      (∑ d ∈ Finset.Icc 0 ⌊x⌋₊, (d : ℝ)⁻¹ * ((moebius d : ℤ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [sum_Icc_zero_remove _ (by simp)]
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

lemma moebius_fractional_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (x / t - (⌊x / t⌋₊ : ℝ)) *
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hi := ((moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x).sub
    (moebius_floor_kernel_intervalIntegrable x hx)
  apply hi.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htne : t ≠ 0 := by linarith [ht.1]
  dsimp only
  field_simp [htne]

theorem moebius_reciprocal_fractional_identity (x : ℝ) (hx : 1 ≤ x) :
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
          ((moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x)
          (moebius_floor_kernel_intervalIntegrable x hx),
          intervalIntegral.integral_const_mul, moebius_logarithmic_floor_integral x hx]
  rw [moebius_reciprocal_abel_identity x hx, he]
  field_simp
  ring

lemma moebius_abs_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) volume 1 x := by
  apply (moebius_summatory_div_intervalIntegrable x hx).abs.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htp : 0 < t := by linarith [ht.1]
  exact abs_div _ t |>.trans (by rw [abs_of_pos htp])

theorem moebius_reciprocal_el_marraki_bound_complete (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        (∫ t in (1 : ℝ)..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) / x +
        Real.log x / x := by
  have hxp : 0 < x := by linarith
  let R : ℝ → ℝ := fun t => (x / t - (⌊x / t⌋₊ : ℝ)) *
    (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t
  have hiR : IntervalIntegrable R volume 1 x :=
    moebius_fractional_kernel_intervalIntegrable x hx
  have hiB := moebius_abs_summatory_div_intervalIntegrable x hx
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
  have hid := moebius_reciprocal_fractional_identity x hx
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

open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        (∫ t in (1 : ℝ)..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) / x +
        Real.log x / x := Helfgott.moebius_reciprocal_el_marraki_bound_complete x hx

#print axioms solution
