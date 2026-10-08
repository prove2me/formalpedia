-- Prove2me | solution 1 for Helfgott.etaPlus_prime_projection_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T10:26:54.177494+00:00
-- url     : https://prove2.me/submissions/04e53e81-1eea-432d-8215-3cb47afec265

import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.PSeries
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_Helfgott_actual_major_kernel_tight_fourier_bounds_complete
import Theorems.Thm_Helfgott_etaPlus_abs_le
import Theorems.Thm_Helfgott_etaPlus_vonMangoldt_summable
import Mathlib.Analysis.Normed.Group.InfiniteSum

section

/-!
Elementary prime-power removal for Helfgott's ternary Goldbach argument,
arXiv:1312.7748v2, §7.4, (7.50). The proper-prime-power injection is adapted
from jjosh's ACCEPTED proof 0afb155e-9279-4986-8c71-52a437e3c0e2 on
Prove2Me (WeakGoldbach.prime_power_part_le_above_2e18). The ternary estimate
and the uniform numerical bound below are derived here. They replace the
quoted Rosser–Schoenfeld estimates by a weaker elementary bound that is
still sufficient at N ≥ 10^27.

Written by Codex.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Helfgott

theorem proper_prime_power_card (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun x => IsPrimePow x ∧ ¬ x.Prime)).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  classical
  rw [← Finset.card_range (Nat.sqrt N + 1),
    ← Finset.card_range (Nat.log 2 N + 1), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun x => (x.minFac, x.factorization x.minFac))
  · intro x hx
    obtain ⟨hxr, hpp, hnp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hxm : x ≤ N := by
      have := Finset.mem_range.mp hxr
      omega
    have hxpos : 0 < x := hpp.pos
    have hxne1 : x ≠ 1 := fun h1 => not_isPrimePow_one (h1 ▸ hpp)
    have hminp : x.minFac.Prime := Nat.minFac_prime hxne1
    have hmin2 : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self hxpos hnp
    have hfact_eq : x.minFac ^ x.factorization x.minFac = x :=
      hpp.minFac_pow_factorization_eq
    have hminfac_le : x.minFac ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      calc x.minFac * x.minFac = x.minFac ^ 2 := by ring
        _ ≤ x := hmin2
        _ ≤ N := hxm
    have h2e : 2 ^ x.factorization x.minFac ≤ N := by
      calc 2 ^ x.factorization x.minFac
          ≤ x.minFac ^ x.factorization x.minFac :=
            Nat.pow_le_pow_left (Nat.Prime.two_le hminp) _
        _ = x := hfact_eq
        _ ≤ N := hxm
    have hele : x.factorization x.minFac ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) h2e
    apply Finset.mem_coe.mpr
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hminfac_le),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hele)⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    have hx₁' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₁)
    have hx₂' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₂)
    have e1 : x₁.minFac ^ x₁.factorization x₁.minFac = x₁ :=
      hx₁'.2.1.minFac_pow_factorization_eq
    have e2 : x₂.minFac ^ x₂.factorization x₂.minFac = x₂ :=
      hx₂'.2.1.minFac_pow_factorization_eq
    have hmf : x₁.minFac = x₂.minFac := congrArg Prod.fst heq
    have hexp : x₁.factorization x₁.minFac = x₂.factorization x₂.minFac :=
      congrArg Prod.snd heq
    rw [hmf] at hexp
    calc x₁ = x₁.minFac ^ x₁.factorization x₁.minFac := e1.symm
      _ = x₂.minFac ^ x₂.factorization x₂.minFac := by rw [hmf, hexp]
      _ = x₂ := e2

/-- The deliberately crude elementary bound leaves ample room below the
paper's positive weighted main term, 0.000422 N². -/
theorem prime_power_error_small (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    2 * 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ) *
        ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ 3
      ≤ (1 / 5000 : ℝ) * (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  set y : ℝ := (N : ℝ) ^ (1 / 16 : ℝ) with hydef
  have hypos : 0 < y := Real.rpow_pos_of_pos hNpos _
  have hy16 : y ^ (16 : ℕ) = N := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hy40 : (40 : ℝ) ≤ y := by
    have hbase : (40 : ℝ) ^ (16 : ℕ) ≤ N := by
      calc _ ≤ (10 : ℝ) ^ 27 := by norm_num
        _ ≤ N := hNreal
    calc (40 : ℝ) = ((40 : ℝ) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 40)]
          norm_num
      _ ≤ y := Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hlogy : Real.log y ≤ y / 8 := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hypos (by norm_num : (0 : ℝ) < 64))
    rw [Real.log_div hypos.ne' (by norm_num : (64 : ℝ) ≠ 0)] at ht
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog64] at ht
    have hlog2 : Real.log 2 < (7 / 10 : ℝ) :=
      lt_trans Real.log_two_lt_d9 (by norm_num)
    linarith
  have hlogN : Real.log (N : ℝ) = 16 * Real.log y := by
    rw [← hy16, Real.log_pow]
    norm_num
  have hL : Real.log (N : ℝ) ≤ 2 * y := by rw [hlogN]; linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hnatlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have hp : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 N) hp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  have hlog2low : (2 / 3 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hnatlog' : (Nat.log 2 N : ℝ) + 1 ≤ 4 * y := by
    have hnn : (0 : ℝ) ≤ Nat.log 2 N := by positivity
    nlinarith
  have hsqrt : (Nat.sqrt N : ℝ) ≤ y ^ 8 := by
    have hsq : (Nat.sqrt N : ℝ) ^ 2 ≤ N := by
      have hsq' : Nat.sqrt N ^ 2 ≤ N := by simpa only [pow_two] using Nat.sqrt_le N
      exact_mod_cast hsq'
    have heq : (y ^ (8 : ℕ)) ^ 2 = N := by rw [← pow_mul]; norm_num; exact hy16
    nlinarith [sq_nonneg (Nat.sqrt N : ℝ), pow_nonneg hypos.le 8]
  have hy8one : (1 : ℝ) ≤ y ^ (8 : ℕ) := one_le_pow₀ hy1
  have hy9one : (1 : ℝ) ≤ y ^ (9 : ℕ) := one_le_pow₀ hy1
  have hsqrt' : (Nat.sqrt N : ℝ) + 1 ≤ 2 * y ^ 8 := by linarith
  have hcount : (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ)
      ≤ 10 * y ^ 9 := by
    push_cast
    have hmul := mul_le_mul hsqrt' hnatlog' (by positivity) (by positivity)
    have heq : (2 * y ^ 8) * (4 * y) = 8 * y ^ 9 := by ring
    rw [heq] at hmul
    linarith
  have hNsucc : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hLcube : Real.log (N : ℝ) ^ 3 ≤ (2 * y) ^ 3 :=
    pow_le_pow_left₀ hL0 hL 3
  have hprod : 2 * 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ) *
        ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ 3
      ≤ 960 * (N : ℝ) * y ^ 12 := by
    calc _ ≤ 2 * 3 * (10 * y ^ 9) * (2 * (N : ℝ)) * (2 * y) ^ 3 := by
          apply mul_le_mul
          · apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hcount (by norm_num)
            · exact hNsucc
            · positivity
            · positivity
          · exact hLcube
          · positivity
          · positivity
      _ = _ := by ring
  have hy4 : (5000000 : ℝ) ≤ y ^ (4 : ℕ) := by
    by_contra h
    have hlt := pow_lt_pow_left₀ (lt_of_not_ge h) (pow_nonneg hypos.le 4)
      (by norm_num : (4 : ℕ) ≠ 0)
    have heq : (y ^ (4 : ℕ)) ^ (4 : ℕ) = N := by
      rw [← pow_mul]
      norm_num
      exact hy16
    rw [heq] at hlt
    norm_num at hlt
    norm_num at hNreal
    linarith
  have hfinal : 4800000 * (N : ℝ) * y ^ 12 ≤ (N : ℝ) ^ 2 := by
    calc _ ≤ y ^ 4 * (N : ℝ) * y ^ 12 := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right (by linarith : (4800000 : ℝ) ≤ y ^ 4) hNpos.le
          · positivity
      _ = (N : ℝ) ^ 2 := by rw [← hy16]; ring
  linarith

end Helfgott

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Finset ArithmeticFunction MeasureTheory Set
open scoped BigOperators

namespace Helfgott

lemma log_square_small_rpow (t : ℝ) (ht : 1 ≤ t) :
    (Real.log t)^2 ≤ 144 * t^(1/16 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have h := Real.mul_exp_neg_le_exp_neg_one ((1/32 : ℝ)*Real.log t)
  have he : Real.exp (-1 : ℝ) ≤ 3/8 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    nlinarith [Real.exp_one_gt_d9]
  have hprod : ((1/32 : ℝ)*Real.log t) ≤ (3/8)*t^(1/32 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (h.trans he)
      (Real.exp_pos ((1/32 : ℝ)*Real.log t)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hh
    simpa only [Real.rpow_def_of_pos ht0, mul_comm (Real.log t) (1/32 : ℝ)] using hh
  have hl : Real.log t ≤ 12*t^(1/32 : ℝ) := by linarith
  have hs := pow_le_pow_left₀ (Real.log_nonneg ht) hl 2
  have hr : (t^(1/32 : ℝ))^2 = t^(1/16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  simpa only [mul_pow, hr, show (12 : ℝ)^2 = 144 by norm_num] using hs

lemma prime_power_series_ratio_le (p : ℕ) (hp : 2 ≤ p) :
    (p : ℝ)^(-(9/16 : ℝ)) ≤ 7/10 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hbase : (2 : ℝ)^(-(9/16 : ℝ)) ≤ 7/10 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 7/10)
      (by norm_num : (16 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  exact (Real.rpow_le_rpow_of_nonpos (by norm_num) htwo (by norm_num)).trans hbase

lemma prime_power_geometric_bound (p L : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Icc 2 L, ((p : ℝ)^(-(9/16 : ℝ)))^k) ≤
      (10/3 : ℝ)*(p : ℝ)^(-(9/8 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr0 : 0 ≤ (p : ℝ)^(-(9/16 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hr := prime_power_series_ratio_le p hp
  have hr1 : (p : ℝ)^(-(9/16 : ℝ)) < 1 := by linarith
  have hh := geom_sum_Ico_le_of_lt_one (m := 2) (n := L+1) hr0 hr1
  have hsets : Finset.Ico 2 (L+1) = Finset.Icc 2 L := by ext k; simp
  rw [hsets] at hh
  have hs : ((p : ℝ)^(-(9/16 : ℝ)))^2 = (p : ℝ)^(-(9/8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  rw [hs] at hh
  apply hh.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-(p : ℝ)^(-(9/16 : ℝ)))).mpr
  nlinarith [Real.rpow_nonneg hp0.le (-(9/8 : ℝ))]

lemma shifted_pseries_sum_le_sixteen :
    (∑' n : ℕ, ((n+2 : ℕ) : ℝ)^(-(17/16 : ℝ))) ≤ 16 := by
  have hanti : AntitoneOn (fun t : ℝ => t^(-(17/16 : ℝ))) (Ici 1) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
      (by intro t ht; change 1 ≤ t at ht; exact lt_of_lt_of_le zero_lt_one ht)
  have hi : IntegrableOn (fun t : ℝ => t^(-(17/16 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hh := AntitoneOn.tsum_comp_add_le_integral
    (f := fun t : ℝ => t^(-(17/16 : ℝ))) 1 (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hi)
    (by intro t ht; have ht0 : (0 : ℝ) ≤ t := by simp only [Set.mem_Ioi, Nat.cast_one] at ht; linarith
        exact Real.rpow_nonneg ht0 _)
  have he : (∫ t : ℝ in Ioi 1, t^(-(17/16 : ℝ))) = 16 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  simpa only [Nat.add_assoc, show (1+1 : ℕ)=2 by norm_num, Nat.cast_one, he] using hh

lemma finite_pseries_sum_le_sixteen (N : ℕ) :
    (∑ p ∈ Finset.Icc 2 N, (p : ℝ)^(-(17/16 : ℝ))) ≤ 16 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(17/16 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs2 : Summable (fun n : ℕ => ((n+2 : ℕ) : ℝ)^(-(17/16 : ℝ))) :=
    (summable_nat_add_iff 2).mpr hs
  have hsets : Finset.Icc 2 N = Finset.Ico 2 (N+1) := by ext k; simp
  rw [hsets, Finset.sum_Ico_eq_sum_range]
  have hh := hs2.sum_le_tsum (Finset.range (N+1-2))
    (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply le_trans ?_ shifted_pseries_sum_le_sixteen
  simpa only [Nat.add_comm 2] using hh

lemma weighted_prime_power_geometric_bound (p L : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.Icc 2 L, (Real.log (p : ℝ))^2 *
      ((p : ℝ)^(-(9/16 : ℝ)))^k) ≤ 480*(p : ℝ)^(-(17/16 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  rw [← Finset.mul_sum]
  calc
    _ ≤ (Real.log (p : ℝ))^2*((10/3 : ℝ)*(p : ℝ)^(-(9/8 : ℝ))) :=
      mul_le_mul_of_nonneg_left (prime_power_geometric_bound p L hp) (sq_nonneg _)
    _ ≤ (144*(p : ℝ)^(1/16 : ℝ))*((10/3 : ℝ)*(p : ℝ)^(-(9/8 : ℝ))) :=
      mul_le_mul_of_nonneg_right (log_square_small_rpow (p : ℝ) hp1) (by positivity)
    _ = _ := by
      rw [show (144*(p : ℝ)^(1/16 : ℝ))*((10/3 : ℝ)*(p : ℝ)^(-(9/8 : ℝ))) =
        480*((p : ℝ)^(1/16 : ℝ)*(p : ℝ)^(-(9/8 : ℝ))) by ring,
        ← Real.rpow_add hp0]
      norm_num

lemma proper_prime_power_dirichlet_partial_sum_le (N : ℕ) :
    (∑ n ∈ Finset.range N, if IsPrimePow n ∧ ¬Nat.Prime n then
      (vonMangoldt n)^2 * (n : ℝ)^(-(9/16 : ℝ)) else 0) ≤ 7680 := by
  classical
  let A := (Finset.range N).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n)
  let f (n : ℕ) := (n.minFac, n.factorization n.minFac)
  let w (t : ℕ × ℕ) : ℝ :=
    (Real.log (t.1 : ℝ))^2 * ((t.1 : ℝ)^(-(9/16 : ℝ)))^t.2
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro n hn m hm he
    have hn' := (Finset.mem_filter.mp hn).2.1
    have hm' := (Finset.mem_filter.mp hm).2.1
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    exact (hn'.minFac_pow_factorization_eq).symm.trans
      ((congrArg₂ (fun p k : ℕ => p^k) he1 he2).trans hm'.minFac_pow_factorization_eq)
  have hmem (n : ℕ) (hn : n ∈ A) :
      f n ∈ (Finset.Icc 2 N) ×ˢ (Finset.Icc 2 (Nat.log 2 N)) := by
    obtain ⟨hnr,hpp,hnp⟩ := Finset.mem_filter.mp hn
    have hnN : n ≤ N := (Finset.mem_range.mp hnr).le
    have hp : n.minFac.Prime := Nat.minFac_prime
      (fun hh => not_isPrimePow_one (hh ▸ hpp))
    have heq := hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ n.factorization n.minFac := by
      by_contra h
      have hlt : n.factorization n.minFac < 2 := by omega
      interval_cases hh : n.factorization n.minFac
      · simp only [hh, pow_zero] at heq
        exact not_isPrimePow_one (heq.symm ▸ hpp)
      · simp only [hh, pow_one] at heq
        exact hnp (heq ▸ hp)
    have hpow : 2^(n.factorization n.minFac) ≤ N :=
      (Nat.pow_le_pow_left hp.two_le _).trans (heq.le.trans hnN)
    have hkl : n.factorization n.minFac ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) hpow
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp.two_le,(Nat.minFac_le hpp.pos).trans hnN⟩,Finset.mem_Icc.mpr ⟨hk2,hkl⟩⟩
  have hvalue (n : ℕ) (hn : n ∈ A) :
      (vonMangoldt n)^2*(n : ℝ)^(-(9/16 : ℝ)) = w (f n) := by
    have hpp := (Finset.mem_filter.mp hn).2.1
    have hp0 : (0 : ℝ) ≤ n.minFac := Nat.cast_nonneg _
    dsimp [w,f]
    rw [vonMangoldt_apply, if_pos hpp,
      Real.rpow_pow_comm hp0, ← Nat.cast_pow, hpp.minFac_pow_factorization_eq]
  rw [← Finset.sum_filter]
  change (∑ n ∈ A, (vonMangoldt n)^2*(n : ℝ)^(-(9/16 : ℝ))) ≤ 7680
  calc
    _ = ∑ n ∈ A, w (f n) := Finset.sum_congr rfl hvalue
    _ = ∑ t ∈ A.image f, w t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ (Finset.Icc 2 N) ×ˢ (Finset.Icc 2 (Nat.log 2 N)), w t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
        exact hmem n hn
      · intro t ht hn
        dsimp [w]
        positivity
    _ = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 (Nat.log 2 N),
        (Real.log (p : ℝ))^2 * ((p : ℝ)^(-(9/16 : ℝ)))^k :=
      Finset.sum_product ..
    _ ≤ ∑ p ∈ Finset.Icc 2 N, 480*(p : ℝ)^(-(17/16 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact weighted_prime_power_geometric_bound p _ (Finset.mem_Icc.mp hp).1
    _ ≤ 480*16 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (finite_pseries_sum_le_sixteen N) (by norm_num)
    _ = 7680 := by norm_num

theorem proper_prime_power_dirichlet_square_energy_summable :
    Summable (fun n : ℕ => if IsPrimePow n ∧ ¬Nat.Prime n then
      (vonMangoldt n)^2 * (n : ℝ)^(-(9/16 : ℝ)) else 0) := by
  classical
  apply summable_of_sum_range_le (c := 7680)
    (fun n => by split_ifs <;> positivity)
  exact proper_prime_power_dirichlet_partial_sum_le

theorem proper_prime_power_dirichlet_square_energy_le :
    (∑' n : ℕ, if IsPrimePow n ∧ ¬Nat.Prime n then
      (vonMangoldt n)^2 * (n : ℝ)^(-(9/16 : ℝ)) else 0) ≤ 7680 := by
  classical
  apply Real.tsum_le_of_sum_range_le (fun n => by split_ifs <;> positivity)
  exact proper_prime_power_dirichlet_partial_sum_le

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logMajorKernel (u : ℝ) : ℝ := majorKernel (Real.exp u)

private noncomputable def logKernelBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^3*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelDBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelD2Body (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)*
    (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
      Real.exp (Real.exp u-1/2)

noncomputable def logMajorKernelD (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelDBody u

noncomputable def logMajorKernelD2 (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelD2Body u

private lemma logKernelBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelBody (logKernelDBody u) u := by
  have h := Real.hasDerivAt_exp u
  convert! ((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 3)).mul
    ((h.sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [logKernelBody,logKernelDBody] <;> ring

private lemma logKernelDBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelDBody (logKernelD2Body u) u := by
  have h := Real.hasDerivAt_exp u
  convert! (((((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 2)).mul
    (h.add_const 4)).mul ((hasDerivAt_const u (1 : ℝ)).sub h)).mul
      ((h.sub_const (1/2 : ℝ)).exp)) using 1 <;>
    dsimp [logKernelDBody,logKernelD2Body] <;> ring

private lemma indicator_Iic_hasDerivAt (f df : ℝ → ℝ) (c : ℝ)
    (hd : ∀ u, HasDerivAt f (df u) u) (hfc : f c = 0) (hdfc : df c = 0) (u : ℝ) :
    HasDerivAt ((Iic c).indicator f) ((Iic c).indicator df u) u := by
  by_cases hu : u ≤ c
  · rw [Set.indicator_of_mem (show u ∈ Iic c from hu)]
    by_cases heq : u = c
    · subst u
      rw [hdfc]
      have hin : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c) c := by
        have h := (hd c).hasDerivWithinAt (s := Iic c)
        rw [hdfc] at h
        apply h.congr
        · intro t ht; simp [Set.indicator_of_mem ht]
        · simp [hfc]
      have hout : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c)ᶜ c := by
        apply (hasDerivAt_const c (0 : ℝ)).hasDerivWithinAt.congr
        · intro t ht; simp [Set.indicator_of_notMem ht]
        · simp [hfc]
      simpa only [union_compl_self,hasDerivWithinAt_univ] using hin.union hout
    · have hlt : u < c := lt_of_le_of_ne hu heq
      apply (hd u).congr_of_eventuallyEq
      filter_upwards [Iic_mem_nhds hlt] with t ht
      simp [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem (show u ∉ Iic c from hu)]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Iic.isOpen_compl.mem_nhds hu] with t ht
    simp [Set.indicator_of_notMem ht]

lemma logMajorKernel_eq_indicator :
    logMajorKernel = (Iic (Real.log 2)).indicator logKernelBody := by
  funext u
  have he : Real.exp u ≤ 2 ↔ u ≤ Real.log 2 := by
    have htwo : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
    constructor
    · intro h
      apply Real.exp_le_exp.mp
      rw [htwo]
      exact h
    · intro h
      simpa only [htwo] using Real.exp_le_exp.mpr h
  by_cases hu : u ≤ Real.log 2
  · have ht : Real.exp u ∈ Icc (0 : ℝ) 2 := ⟨(Real.exp_pos _).le,he.mpr hu⟩
    simp [logMajorKernel,majorKernel,Set.indicator_of_mem ht,
      Set.indicator_of_mem (show u ∈ Iic (Real.log 2) from hu),logKernelBody]
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu (he.mp h.2)
    simp [logMajorKernel,majorKernel,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem (show u ∉ Iic (Real.log 2) from hu)]

theorem logMajorKernel_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernel (logMajorKernelD u) u := by
  rw [logMajorKernel_eq_indicator]
  exact indicator_Iic_hasDerivAt logKernelBody logKernelDBody (Real.log 2)
    logKernelBody_hasDerivAt (by norm_num [logKernelBody,Real.exp_log])
    (by norm_num [logKernelDBody,Real.exp_log]) u

theorem logMajorKernelD_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernelD (logMajorKernelD2 u) u := by
  exact indicator_Iic_hasDerivAt logKernelDBody logKernelD2Body (Real.log 2)
    logKernelDBody_hasDerivAt (by norm_num [logKernelDBody,Real.exp_log])
    (by norm_num [logKernelD2Body,Real.exp_log]) u

lemma logMajorKernel_continuous : Continuous logMajorKernel :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernel_hasDerivAt u).continuousAt)

lemma logMajorKernelD_continuous : Continuous logMajorKernelD :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernelD_hasDerivAt u).continuousAt)

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

lemma integral_comp_exp_univ (g : ℝ → ℝ) :
    (∫ u : ℝ, Real.exp u*g (Real.exp u)) = ∫ t in Ioi (0 : ℝ), g t := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

lemma integrable_comp_exp_univ (g : ℝ → ℝ) :
    Integrable (fun u : ℝ => Real.exp u*g (Real.exp u)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [integrableOn_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logKernelDensity (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)^2*(t+4)*(1-t)*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD2 (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)) t

private lemma exp_mem_interval (u : ℝ) :
    Real.exp u ∈ Icc (0 : ℝ) 2 ↔ u ∈ Iic (Real.log 2) := by
  have ht : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
  constructor
  · intro h
    apply Real.exp_le_exp.mp
    simpa only [ht] using h.2
  · intro h
    exact ⟨(Real.exp_pos _).le,by simpa only [ht] using Real.exp_le_exp.mpr h⟩

lemma logMajorKernel_density (u : ℝ) :
    logMajorKernel u = Real.exp u*logKernelDensity (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_mem ht]
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_notMem ht]

lemma logMajorKernelD_density (u : ℝ) :
    logMajorKernelD u = Real.exp u*logKernelDensityD (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD,logKernelDensityD,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*
      Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD,logKernelDensityD,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

lemma logMajorKernelD2_density (u : ℝ) :
    logMajorKernelD2 u = Real.exp u*logKernelDensityD2 (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)*
      (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
        Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

private lemma integrable_interval_density (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : f 0 = 0) (h2 : f 2 = 0) :
    Integrable ((Icc (0 : ℝ) 2).indicator f) := by
  have hc : Continuous ((Icc (0 : ℝ) 2).indicator f) := by
    apply continuous_indicator
    · intro t ht
      have hb := frontier_subset_closure ht
      rw [isClosed_Icc.closure_eq] at hb
      have hn : t ∉ interior (Icc (0 : ℝ) 2) := ht.2
      rw [interior_Icc] at hn
      have he : t=0 ∨ t=2 := by
        by_contra hh
        apply hn
        have h0 : t ≠ 0 := by tauto
        have h2 : t ≠ 2 := by tauto
        exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0),lt_of_le_of_ne hb.2 h2⟩
      rcases he with rfl | rfl <;> assumption
    · exact hf.continuousOn
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  exact Set.indicator_of_notMem ht f

lemma logKernelDensity_integrable : Integrable logKernelDensity := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD_integrable : Integrable logKernelDensityD := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD2_integrable : Integrable logKernelDensityD2 := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logMajorKernel_integrable : Integrable logMajorKernel := by
  have h := (integrable_comp_exp_univ logKernelDensity).mpr
    logKernelDensity_integrable.integrableOn
  simpa only [← logMajorKernel_density] using h

lemma logMajorKernelD_integrable : Integrable logMajorKernelD := by
  have h := (integrable_comp_exp_univ logKernelDensityD).mpr
    logKernelDensityD_integrable.integrableOn
  simpa only [← logMajorKernelD_density] using h

lemma logMajorKernelD2_integrable : Integrable logMajorKernelD2 := by
  have h := (integrable_comp_exp_univ logKernelDensityD2).mpr
    logKernelDensityD2_integrable.integrableOn
  simpa only [← logMajorKernelD2_density] using h

lemma logMajorKernelD2_abs_integral :
    (∫ u : ℝ, |logMajorKernelD2 u|) = ∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t| := by
  simpa only [logMajorKernelD2_density,abs_mul,abs_of_pos (Real.exp_pos _)]
    using integral_comp_exp_univ (fun t => |logKernelDensityD2 t|)

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

private noncomputable def variationP (t : ℝ) := t^2*(2-t)^2
private noncomputable def variationPD (t : ℝ) := 4*t*(2-t)*(1-t)
private noncomputable def variationA (t : ℝ) := variationP t*(t+4)*Real.exp (t-1/2)
private noncomputable def variationAD (t : ℝ) :=
  (variationPD t*(t+4)+variationP t*(t+5))*Real.exp (t-1/2)
private noncomputable def variationB (t : ℝ) := (t+4)*(t-1)*Real.exp (t-1/2)
private noncomputable def variationBD (t : ℝ) := (t^2+5*t-1)*Real.exp (t-1/2)
private noncomputable def secondDensityBody (t : ℝ) :=
  t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)

private lemma variationP_hasDerivAt (t : ℝ) :
    HasDerivAt variationP (variationPD t) t := by
  convert! ((hasDerivAt_id t).pow 2).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 2) using 1 <;>
    dsimp [variationP,variationPD] <;> ring

private lemma variationA_hasDerivAt (t : ℝ) :
    HasDerivAt variationA (variationAD t) t := by
  convert! ((variationP_hasDerivAt t).mul ((hasDerivAt_id t).add_const 4)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationA,variationAD] <;> ring

private lemma variationB_hasDerivAt (t : ℝ) :
    HasDerivAt variationB (variationBD t) t := by
  convert! (((hasDerivAt_id t).add_const 4).mul ((hasDerivAt_id t).sub_const 1)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationB,variationBD] <;> ring

private lemma variationP_nonneg (t : ℝ) : 0 ≤ variationP t := by
  dsimp [variationP]; positivity

private lemma variationP_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : variationP t ≤ 1 := by
  have h0 : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
  have h1 : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
  have h2 := mul_nonneg h0 (sub_nonneg.mpr h1)
  dsimp [variationP]
  nlinarith

private lemma first_interval_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |secondDensityBody t| ≤ variationAD t+5*Real.exp (1/2) := by
  have hp : 0 ≤ variationP t := variationP_nonneg t
  have hpd : 0 ≤ variationPD t := by
    dsimp [variationPD]
    have ht0 : 0 ≤ t := ht.1
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ 1-t := by linarith [ht.2]
    positivity
  have had : 0 ≤ variationAD t := by
    dsimp [variationAD]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h5 : 0 ≤ t+5 := by linarith [ht.1]
    positivity
  have ha : 0 ≤ variationA t := by
    dsimp [variationA]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    positivity
  have ha_le : variationA t ≤ 5*Real.exp (1/2) := by
    have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1,by linarith [ht.2]⟩)
    have he : Real.exp (t-1/2) ≤ Real.exp (1/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    dsimp [variationA]
    calc
      _ ≤ 1*5*Real.exp (1/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = variationAD t*(1-t)-variationA t := by
    dsimp [secondDensityBody,variationAD,variationA,variationPD,variationP]
    ring
  rw [heq]
  calc
    _ ≤ |variationAD t*(1-t)|+|variationA t| := abs_sub _ _
    _ = variationAD t*(1-t)+variationA t := by
      rw [abs_of_nonneg (mul_nonneg had (by linarith [ht.2])),abs_of_nonneg ha]
    _ ≤ variationAD t+5*Real.exp (1/2) := by
      have h := mul_nonneg had ht.1
      nlinarith

private lemma second_interval_bound {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    |secondDensityBody t| ≤ (-variationPD t)*(6*Real.exp (3/2))+variationBD t := by
  have hp := variationP_nonneg t
  have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨by linarith [ht.1],ht.2⟩)
  have hpd : 0 ≤ -variationPD t := by
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht0) h2) h1
    dsimp [variationPD]; nlinarith
  have hb : 0 ≤ variationB t := by
    dsimp [variationB]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    positivity
  have hbd : 0 ≤ variationBD t := by
    dsimp [variationBD]
    have hq : 0 ≤ t^2+5*t-1 := by nlinarith [sq_nonneg t,ht.1]
    positivity
  have hb_le : variationB t ≤ 6*Real.exp (3/2) := by
    dsimp [variationB]
    have he : Real.exp (t-1/2) ≤ Real.exp (3/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    calc
      _ ≤ 6*1*Real.exp (3/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = (-variationPD t)*variationB t-variationP t*variationBD t := by
    dsimp [secondDensityBody,variationPD,variationB,variationP,variationBD]; ring
  rw [heq]
  calc
    _ ≤ |(-variationPD t)*variationB t|+|variationP t*variationBD t| := abs_sub _ _
    _ = (-variationPD t)*variationB t+variationP t*variationBD t := by
      rw [abs_of_nonneg (mul_nonneg hpd hb),abs_of_nonneg (mul_nonneg hp hbd)]
    _ ≤ (-variationPD t)*(6*Real.exp (3/2))+1*variationBD t := by gcongr
    _ = _ := by ring

private lemma first_interval_integral :
    (∫ t in (0 : ℝ)..1, |secondDensityBody t|) ≤ 10*Real.exp (1/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 0 1 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hd : IntervalIntegrable variationAD volume 0 1 :=
    (by unfold variationAD variationPD variationP; fun_prop : Continuous variationAD).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => 5*Real.exp (1/2)) volume 0 1 :=
    intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hf (hd.add hc)
    (fun t ht => first_interval_bound ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationA_hasDerivAt t) hd
  rw [intervalIntegral.integral_add hd hc,hi,intervalIntegral.integral_const] at hm
  norm_num [variationA,variationP,smul_eq_mul] at hm ⊢
  linarith

private lemma second_interval_integral :
    (∫ t in (1 : ℝ)..2, |secondDensityBody t|) ≤ 12*Real.exp (3/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 1 2 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hp : IntervalIntegrable variationPD volume 1 2 :=
    (by unfold variationPD; fun_prop : Continuous variationPD).intervalIntegrable _ _
  have hb : IntervalIntegrable variationBD volume 1 2 :=
    (by unfold variationBD; fun_prop : Continuous variationBD).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2) hf
    ((hp.neg.mul_const (6*Real.exp (3/2))).add hb) (fun t ht => second_interval_bound ht)
  have hpi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationP_hasDerivAt t) hp
  have hbi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationB_hasDerivAt t) hb
  rw [intervalIntegral.integral_add (hp.neg.mul_const _) hb,
    intervalIntegral.integral_mul_const] at hm
  simp only [Pi.neg_apply] at hm
  rw [intervalIntegral.integral_neg,hpi,hbi] at hm
  norm_num [variationP,variationB] at hm ⊢
  linarith

private lemma density_abs_interval :
    (∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t|) = ∫ t in (0 : ℝ)..2, |secondDensityBody t| := by
  have h : (fun t => |logKernelDensityD2 t|) = (Icc (0 : ℝ) 2).indicator
      (fun t => |secondDensityBody t|) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 2
    · simp [logKernelDensityD2,secondDensityBody,Set.indicator_of_mem ht]
    · simp [logKernelDensityD2,Set.indicator_of_notMem ht]
  rw [h,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc (0 : ℝ) 2 ∩ Ioi 0 = Ioc 0 2 := by ext t; simp; constructor <;> intro h <;> grind
  rw [hs,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

theorem logMajorKernelD2_abs_integral_le : (∫ u : ℝ, |logMajorKernelD2 u|) ≤ 80 := by
  rw [logMajorKernelD2_abs_integral,density_abs_interval]
  have hc : Continuous (fun t => |secondDensityBody t|) := by dsimp [secondDensityBody]; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2)]
  have he1 : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have hs : (Real.exp (1/2 : ℝ))^2 = Real.exp 1 := by
      rw [sq,← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9,Real.exp_pos (1/2 : ℝ)]
  have he3 : Real.exp (3/2 : ℝ) ≤ 9/2 := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.exp_add]
    calc
      _ ≤ (27183/10000 : ℝ)*(33/20) := by
        gcongr
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ _ := by norm_num
  linarith [first_interval_integral,second_interval_integral]

end Helfgott

end

section

open MeasureTheory
open scoped FourierTransform

namespace Helfgott

theorem fourier_second_derivative_decay {f f₁ f₂ : ℝ → ℂ}
    (h₀ : Integrable f) (h₁ : Integrable f₁) (h₂ : Integrable f₂)
    (hd₀ : ∀ u, HasDerivAt f (f₁ u) u) (hd₁ : ∀ u, HasDerivAt f₁ (f₂ u) u)
    (ξ : ℝ) :
    (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ ≤ ∫ u : ℝ, ‖f₂ u‖ := by
  have he₀ : deriv f = f₁ := funext (fun u => (hd₀ u).deriv)
  have he₁ : deriv f₁ = f₂ := funext (fun u => (hd₁ u).deriv)
  have hf₀ := congrFun (Real.fourier_deriv h₀ (fun u => (hd₀ u).differentiableAt)
    (by rw [he₀]; exact h₁)) ξ
  rw [he₀] at hf₀
  have hf₁ := congrFun (Real.fourier_deriv h₁ (fun u => (hd₁ u).differentiableAt)
    (by rw [he₁]; exact h₂)) ξ
  rw [he₁] at hf₁
  have hidentity : 𝓕 f₂ ξ = ((2*Real.pi*Complex.I*(ξ : ℂ))^2)*𝓕 f ξ := by
    rw [hf₁,hf₀]
    simp only [smul_eq_mul,pow_two,mul_assoc]
  have hn : ‖𝓕 f₂ ξ‖ = (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ := by
    rw [hidentity,norm_mul,norm_pow]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [← hn,Real.fourier_eq]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f₂ ξ

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma integrable_of_quadratic_decay (F : ℝ → ℂ) (hc : Continuous F) (A C : ℝ)
    (hb : ∀ ξ : ℝ, ‖F ξ‖ ≤ A) (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) : Integrable F := by
  apply (integrable_inv_one_add_sq.const_mul (A+C)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun ξ => by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+ξ^2)).mpr
    nlinarith [hb ξ,hd ξ])

lemma inv_square_integrableOn {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ξ : ℝ => (ξ^2)⁻¹) (Ioi R) := by
  simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR

lemma inv_square_integral {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, (ξ^2)⁻¹) = R⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR
  norm_num [Real.rpow_neg_one] at h
  exact h

lemma quadratic_decay_right_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, ‖F ξ‖) ≤ C/R := by
  calc
    _ ≤ ∫ ξ in Ioi R, C*(ξ^2)⁻¹ := by
      apply setIntegral_mono_on hi.norm.integrableOn ((inv_square_integrableOn hR).const_mul C)
        measurableSet_Ioi
      intro ξ hξ
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (sq_pos_of_pos (hR.trans hξ))).mpr
      nlinarith [hd ξ]
    _ = C/R := by rw [integral_const_mul,inv_square_integral hR,div_eq_mul_inv]

lemma integral_left_tail (F : ℝ → ℝ) (R : ℝ) :
    (∫ ξ in Iio (-R), F ξ) = ∫ ξ in Ioi R, F (-ξ) := by
  have him : (fun ξ : ℝ => -ξ) '' Ioi R = Iio (-R) := by
    ext ξ
    simp only [mem_image,mem_Ioi,mem_Iio]
    constructor
    · rintro ⟨u,hu,rfl⟩; linarith
    · intro h; exact ⟨-ξ,by linarith,by simp⟩
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi R) measurableSet_Ioi
    (fun ξ _ => (hasDerivAt_id ξ).neg.hasDerivWithinAt)
    (fun ξ _ υ _ h => neg_injective h) F
  simpa using h

lemma quadratic_decay_left_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Iio (-R), ‖F ξ‖) ≤ C/R := by
  rw [integral_left_tail]
  apply quadratic_decay_right_tail (fun ξ => F (-ξ)) hi.comp_neg C _ hR
  intro ξ
  simpa only [neg_sq] using hd (-ξ)

noncomputable def logKernelComplex (u : ℝ) : ℂ := (logMajorKernel u : ℂ)

lemma logKernelComplex_integrable : Integrable logKernelComplex :=
  Complex.ofRealCLM.integrable_comp logMajorKernel_integrable

lemma logKernelComplex_continuous : Continuous logKernelComplex :=
  Complex.continuous_ofReal.comp logMajorKernel_continuous

lemma logKernelComplex_fourier_decay (ξ : ℝ) :
    ξ^2*‖𝓕 logKernelComplex ξ‖ ≤ 80/(4*Real.pi^2) := by
  have h := fourier_second_derivative_decay logKernelComplex_integrable
    (Complex.ofRealCLM.integrable_comp logMajorKernelD_integrable)
    (Complex.ofRealCLM.integrable_comp logMajorKernelD2_integrable)
    (fun u => (logMajorKernel_hasDerivAt u).ofReal_comp)
    (fun u => (logMajorKernelD_hasDerivAt u).ofReal_comp) ξ
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs] at h
  have hm := logMajorKernelD2_abs_integral_le
  have he : (2*Real.pi*|ξ|)^2 = (4*Real.pi^2)*ξ^2 := by
    nlinarith [sq_abs ξ]
  rw [he] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi^2)).mpr
  nlinarith

lemma logKernelComplex_fourier_integrable : Integrable (𝓕 logKernelComplex) := by
  have hc : Continuous (𝓕 logKernelComplex) := by
    have he : 𝓕 logKernelComplex = VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) logKernelComplex := by
      funext ξ
      rw [Real.fourier_eq]
      rfl
    rw [he]
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2))
      logKernelComplex_integrable
  apply integrable_of_quadratic_decay _ hc (∫ u : ℝ, ‖logKernelComplex u‖) (80/(4*Real.pi^2))
  · intro ξ
    rw [Real.fourier_eq]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) logKernelComplex ξ
  · exact logKernelComplex_fourier_decay

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def fourierCutoff (F : ℝ → ℂ) (R u : ℝ) : ℂ :=
  ∫ ξ in Icc (-R) R, Real.fourierChar (inner ℝ ξ u) • F ξ

lemma quadratic_decay_outside (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖) ≤ 2*C/R := by
  have hs : (Icc (-R) R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [mem_compl_iff,mem_Icc,mem_union,mem_Iio,mem_Ioi]
    constructor
    · intro h
      by_cases hx : ξ < -R
      · exact Or.inl hx
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨le_of_not_gt hx,hr⟩))
    · rintro (h | h) ⟨hl,hr⟩
      · exact (not_lt_of_ge hl) h
      · exact (not_lt_of_ge hr) h
  have hj : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hl hr
    simp only [mem_Iio,mem_Ioi] at hl hr
    linarith
  rw [hs,setIntegral_union hj measurableSet_Ioi hi.norm.integrableOn hi.norm.integrableOn]
  rw [show 2*C/R=C/R+C/R by ring]
  exact add_le_add (quadratic_decay_left_tail F hi C hd hR)
    (quadratic_decay_right_tail F hi C hd hR)

lemma fourierCutoff_error (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖fourierCutoff F R u - 𝓕⁻ F u‖ ≤ 2*C/R := by
  have hint : Integrable (fun ξ => Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    apply hi.norm.mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable
    · exact ae_of_all _ (fun ξ => (Circle.norm_smul _ _).le)
  have h := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hint
  have heq : fourierCutoff F R u - 𝓕⁻ F u =
      -(∫ ξ in (Icc (-R) R)ᶜ, Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    rw [fourierCutoff,Real.fourierInv_eq,← h]
    abel
  rw [heq,norm_neg]
  calc
    _ ≤ ∫ ξ in (Icc (-R) R)ᶜ, ‖Real.fourierChar (inner ℝ ξ u) • F ξ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖ := by simp only [Circle.norm_smul]
    _ ≤ _ := quadratic_decay_outside F hi C hd hR

theorem logKernel_fourierCutoff_error {H : ℝ} (hH : 0 < H) (u : ℝ) :
    ‖fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u-logKernelComplex u‖ ≤
      80/(Real.pi*H) := by
  have h := fourierCutoff_error (𝓕 logKernelComplex) logKernelComplex_fourier_integrable
    (80/(4*Real.pi^2)) logKernelComplex_fourier_decay
    (div_pos hH (by positivity : (0 : ℝ) < 2*Real.pi)) u
  rw [logKernelComplex_integrable.fourierInv_fourier_eq logKernelComplex_fourier_integrable
    logKernelComplex_continuous.continuousAt] at h
  have he : 2*(80/(4*Real.pi^2))/(H/(2*Real.pi)) = 80/(Real.pi*H) := by
    field_simp
    <;> ring
  rwa [he] at h

end Helfgott

end

section

open MeasureTheory Set
open scoped FourierTransform

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma integral_fourierChar_interval (R v : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, (Real.fourierChar (ξ*v) : ℂ)) =
      ((2*R*Real.sinc (2*Real.pi*R*v) : ℝ) : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  by_cases hv : v=0
  · subst v
    simp [intervalIntegral.integral_const,Complex.real_smul]
    <;> ring
  · have hc : 2*Real.pi*v ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hv
    calc
      _ = ∫ ξ in -R..R, Complex.exp (((ξ*(2*Real.pi*v) : ℝ) : ℂ)*Complex.I) := by
        apply intervalIntegral.integral_congr
        intro ξ _
        dsimp only
        rw [Real.fourierChar_apply]
        congr 2
        push_cast
        ring
      _ = (2*Real.pi*v)⁻¹ • ∫ t in -(R*(2*Real.pi*v))..R*(2*Real.pi*v),
          Complex.exp ((t : ℂ)*Complex.I) := by
        have h := intervalIntegral.integral_comp_mul_right
          (fun t : ℝ => Complex.exp ((t : ℂ)*Complex.I)) (a := -R) (b := R) hc
        simpa only [neg_mul] using h
      _ = (2*Real.pi*v)⁻¹ • (2*(R*(2*Real.pi*v))*Real.sinc (R*(2*Real.pi*v)) : ℂ) := by
        rw [integral_exp_mul_I_eq_sinc]
        push_cast
        rfl
      _ = _ := by
        rw [Complex.real_smul]
        have he : R*(2*Real.pi*v)=2*Real.pi*R*v := by ring
        rw [he]
        push_cast
        have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
        have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp [hvC,hpC]
        <;> ring

lemma fourierCutoff_eq_sinc_convolution (f : ℝ → ℂ) (hi : Integrable f)
    (R u : ℝ) (hR : 0 ≤ R) :
    fourierCutoff (𝓕 f) R u = ∫ v : ℝ,
      ((2*R*Real.sinc (2*Real.pi*R*(u-v)) : ℝ) : ℂ)*f v := by
  let g : ℝ → ℝ → ℂ := fun ξ v => Real.fourierChar (inner ℝ ξ (u-v)) • f v
  have hg : Integrable (Function.uncurry g) ((volume.restrict (Icc (-R) R)).prod volume) := by
    apply (hi.norm.comp_snd (volume.restrict (Icc (-R) R))).mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable.comp_snd
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  have heq : fourierCutoff (𝓕 f) R u = ∫ ξ in Icc (-R) R, ∫ v : ℝ, g ξ v := by
    unfold fourierCutoff
    simp_rw [Real.fourier_eq,Circle.smul_def,smul_eq_mul,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro ξ _
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only [g]
      rw [Circle.smul_def,smul_eq_mul,← mul_assoc,← Circle.coe_mul,← Real.fourierChar.map_add_eq_mul]
      congr 2
      simp only [Real.inner_apply]
      ring)
  rw [heq,integral_integral_swap hg]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [g]
    simp only [Real.inner_apply,Circle.smul_def,smul_eq_mul]
    rw [integral_mul_const,integral_fourierChar_interval R (u-v) hR])

lemma bandLimitedMajorKernel_log_eq (H u : ℝ) :
    bandLimitedMajorKernel H (Real.exp u) = ∫ v : ℝ,
      logMajorKernel (u-v)*(H/Real.pi*Real.sinc (H*v)) := by
  unfold bandLimitedMajorKernel mellinConv
  rw [← integral_comp_exp_univ (fun w => majorKernel (Real.exp u/w)*bandKernel H w/w)]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    unfold logMajorKernel bandKernel
    dsimp only
    rw [Real.log_exp,Real.exp_sub]
    field_simp)

theorem bandLimitedMajorKernel_fourierCutoff (H u : ℝ) (hH : 0 ≤ H) :
    (bandLimitedMajorKernel H (Real.exp u) : ℂ) =
      fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u := by
  rw [fourierCutoff_eq_sinc_convolution _ logKernelComplex_integrable _ _
    (div_nonneg hH (by positivity)),bandLimitedMajorKernel_log_eq]
  rw [← integral_complex_ofReal]
  conv_rhs => rw [← integral_sub_left_eq_self _ volume u]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [logKernelComplex]
    have he : 2*Real.pi*(H/(2*Real.pi))*(u-(u-v))=H*v := by field_simp; ring
    have hc : 2*(H/(2*Real.pi))=H/Real.pi := by field_simp
    rw [he,hc]
    push_cast
    ring)

end Helfgott

end

section
open MeasureTheory Set
open scoped FourierTransform
namespace Helfgott
lemma logKernelComplex_fourier_mass_numerical_bound : (∫ ξ : ℝ,‖𝓕 logKernelComplex ξ‖) ≤ 25/6 := by
  have h := actual_major_kernel_tight_fourier_bounds_complete.2.2.2.2
  change (∫ ξ : ℝ,‖𝓕 (fun u : ℝ => (majorKernel (Real.exp u) : ℂ)) ξ‖) ≤ 25/6
  exact h
end Helfgott
end

section
open MeasureTheory Set
namespace Helfgott
lemma majorKernel_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : majorKernel t = 0 := by
  by_cases hz : t = 0
  · subst t; simp [majorKernel]
  · have hn : t ∉ Icc (0 : ℝ) 2 := by intro h; exact hz (le_antisymm ht h.1)
    simp [majorKernel,hn]
lemma bandLimitedMajorKernel_zero_of_nonpos (H t : ℝ) (ht : t ≤ 0) :
    bandLimitedMajorKernel H t = 0 := by
  unfold bandLimitedMajorKernel mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [majorKernel_zero_of_nonpos (t/w) (div_nonpos_of_nonpos_of_nonneg ht hw.le)]
  simp
end Helfgott
end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma bandLimitedMajorKernel_numerical_envelope (t : ℝ) :
    |bandLimitedMajorKernel 200 t| ≤ 25/6 := by
  by_cases ht : 0 < t
  · have he := bandLimitedMajorKernel_fourierCutoff 200 (Real.log t) (by norm_num)
    rw [Real.exp_log ht] at he
    have hn : |bandLimitedMajorKernel 200 t| = ‖(bandLimitedMajorKernel 200 t : ℂ)‖ :=
      (by simp only [Complex.norm_real, Real.norm_eq_abs])
    rw [hn, he, fourierCutoff]
    calc
      _ ≤ ∫ ξ in Icc (-(200/(2*Real.pi) : ℝ)) (200/(2*Real.pi)),
          ‖Real.fourierChar (inner ℝ ξ (Real.log t)) • 𝓕 logKernelComplex ξ‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ ξ in Icc (-(200/(2*Real.pi) : ℝ)) (200/(2*Real.pi)),
          ‖𝓕 logKernelComplex ξ‖ := by simp only [Circle.norm_smul]
      _ ≤ ∫ ξ : ℝ, ‖𝓕 logKernelComplex ξ‖ :=
        setIntegral_le_integral logKernelComplex_fourier_integrable.norm
          (ae_of_all _ (fun ξ => norm_nonneg _))
      _ ≤ 25/6 := logKernelComplex_fourier_mass_numerical_bound
  · rw [bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht), abs_zero]
    norm_num

lemma etaPlus_numerical_gaussian_envelope (t : ℝ) :
    |etaPlus t| ≤ (25/6 : ℝ)*|t| * Real.exp (-(t^2)/2) := by
  rw [etaPlus, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (bandLimitedMajorKernel_numerical_envelope t) (abs_nonneg _))
    (Real.exp_pos _).le

lemma gaussian_fourth_factor_le_one (t : ℝ) : t^4*Real.exp (-(t^2)) ≤ 1 := by
  have he : Real.exp (-1 : ℝ) ≤ 3/8 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    nlinarith [Real.exp_one_gt_d9]
  have hh := (Real.mul_exp_neg_le_exp_neg_one (t^2/2)).trans he
  have hn : 0 ≤ t^2/2*Real.exp (-(t^2/2)) := by positivity
  have hs := pow_le_pow_left₀ hn hh 2
  have hx : (Real.exp (-(t^2/2)))^2 = Real.exp (-(t^2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hx] at hs
  nlinarith

theorem etaPlus_square_rpow_envelope (t : ℝ) (ht : 0 ≤ t) :
    (etaPlus t)^2*t^(9/16 : ℝ) ≤ 18 := by
  by_cases ht1 : t ≤ 1
  · have hh := pow_le_pow_left₀ (abs_nonneg (etaPlus t)) (etaPlus_abs_le t) 2
    rw [sq_abs] at hh
    have hr := Real.rpow_le_one ht ht1 (by norm_num : (0 : ℝ) ≤ 9/16)
    have hmul := mul_le_mul_of_nonneg_left hr (sq_nonneg (etaPlus t))
    norm_num at hh
    nlinarith
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hh := pow_le_pow_left₀ (abs_nonneg (etaPlus t)) (etaPlus_numerical_gaussian_envelope t) 2
    have he : (Real.exp (-(t^2)/2))^2 = Real.exp (-(t^2)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [sq_abs, mul_pow, mul_pow, sq_abs, he] at hh
    have hr : t^(9/16 : ℝ) ≤ t^2 := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le ht1' (by norm_num : (9/16 : ℝ) ≤ (2 : ℕ))
    calc
      _ ≤ ((25/6 : ℝ)^2*t^2*Real.exp (-(t^2)))*t^(9/16 : ℝ) :=
        mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ht _)
      _ ≤ ((25/6 : ℝ)^2*t^2*Real.exp (-(t^2)))*t^2 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (25/6 : ℝ)^2*(t^4*Real.exp (-(t^2))) := by ring
      _ ≤ (25/6 : ℝ)^2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (gaussian_fourth_factor_le_one t) (sq_nonneg (25/6 : ℝ))
      _ ≤ 18 := by norm_num

lemma etaPlus_scaled_square_envelope (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    (etaPlus ((n : ℝ)/x))^2 ≤
      18*x^(9/16 : ℝ)*(n : ℝ)^(-(9/16 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := div_pos hnR hx
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos ht (9/16 : ℝ))).mpr
    (etaPlus_square_rpow_envelope ((n : ℝ)/x) ht.le)
  apply hh.trans_eq
  rw [Real.div_rpow hnR.le hx.le, div_eq_mul_inv, inv_div, Real.rpow_neg hnR.le]
  ring

end Helfgott

end

section
namespace Helfgott
lemma etaPlus_vonMangoldt_complex_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)*
      (etaPlus ((n : ℝ)/x) : ℂ)) := by
  have h := Complex.summable_ofReal.mpr (etaPlus_vonMangoldt_summable x hx)
  simpa only [Complex.ofReal_mul] using h
end Helfgott
end

section
namespace Helfgott
lemma coefficient_square_summable (c : ℕ → ℂ) (hc : Summable c) : Summable (fun n => ‖c n‖^2) := by
  have hh := (hc.norm.mul_norm hc.norm).comp_injective
    (show Function.Injective (fun n : ℕ => (n,n)) from fun m n h => congrArg Prod.fst h)
  simpa [Function.comp_def,norm_mul,pow_two] using hh
end Helfgott
end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Finset ArithmeticFunction MeasureTheory
open scoped BigOperators Classical

namespace Helfgott

lemma etaPlus_coefficient_square (x : ℝ) (n : ℕ) :
    ‖((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ)‖^2 =
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]

lemma etaPlus_small_indices_square_energy_le (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0) ≤ 100*x^(9/16 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by norm_num; exact hx)
  have hlog : (Real.log (Real.sqrt x))^2 ≤ 36*x^(1/16 : ℝ) := by
    rw [Real.log_sqrt hx0.le]
    nlinarith [log_square_small_rpow x hx]
  have hcut : (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0) =
      ∑ n ∈ Finset.range (Nat.floor (Real.sqrt x)+1),
        (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 := by
    rw [tsum_eq_sum (s := Finset.range (Nat.floor (Real.sqrt x)+1))]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnfl : n ≤ Nat.floor (Real.sqrt x) := by
        have hh := Finset.mem_range.mp hn
        omega
      rw [if_pos ((Nat.le_floor_iff (Real.sqrt_nonneg x)).mp hnfl)]
    · intro n hn
      have hnf : ¬n ≤ Nat.floor (Real.sqrt x) := by
        have hh : ¬n < Nat.floor (Real.sqrt x)+1 := by simpa only [Finset.mem_range] using hn
        omega
      exact if_neg (fun h => hnf ((Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr h))
  have hpoint (n : ℕ) (hn : n ∈ Finset.range (Nat.floor (Real.sqrt x)+1)) :
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 ≤ (6/5 : ℝ)*36*x^(1/16 : ℝ) := by
    by_cases hn0 : n = 0
    · subst n
      simp
      positivity
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnfl : n ≤ Nat.floor (Real.sqrt x) := by
      have hh := Finset.mem_range.mp hn
      omega
    have hnle := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mp hnfl
    have hl : vonMangoldt n ≤ Real.log (Real.sqrt x) :=
      vonMangoldt_le_log.trans (Real.log_le_log hnpos hnle)
    have hl2 := pow_le_pow_left₀ vonMangoldt_nonneg hl 2
    have he : (etaPlus ((n : ℝ)/x))^2 ≤ (6/5 : ℝ) := by
      have hh := pow_le_pow_left₀ (abs_nonneg (etaPlus ((n : ℝ)/x))) (etaPlus_abs_le _) 2
      rw [sq_abs] at hh
      norm_num at hh
      linarith
    calc
      _ ≤ (Real.log (Real.sqrt x))^2*(6/5 : ℝ) :=
        mul_le_mul hl2 he (sq_nonneg _) (sq_nonneg _)
      _ ≤ (36*x^(1/16 : ℝ))*(6/5 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog (by norm_num)
      _ = _ := by ring
  rw [hcut]
  calc
    _ ≤ ∑ n ∈ Finset.range (Nat.floor (Real.sqrt x)+1), (6/5 : ℝ)*36*x^(1/16 : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = ((Nat.floor (Real.sqrt x)+1 : ℕ) : ℝ)*((6/5 : ℝ)*36*x^(1/16 : ℝ)) := by simp
    _ ≤ (2*Real.sqrt x)*((6/5 : ℝ)*36*x^(1/16 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      push_cast
      linarith [Nat.floor_le (Real.sqrt_nonneg x)]
    _ = (432/5 : ℝ)*x^(9/16 : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (2*x^(1/2 : ℝ))*((6/5 : ℝ)*36*x^(1/16 : ℝ)) =
        (432/5 : ℝ)*(x^(1/2 : ℝ)*x^(1/16 : ℝ)) by ring, ←Real.rpow_add hx0]
      norm_num
    _ ≤ 100*x^(9/16 : ℝ) := by gcongr; norm_num

lemma etaPlus_proper_prime_power_square_energy_le (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, if IsPrimePow n ∧ ¬Nat.Prime n then
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0) ≤ 138240*x^(9/16 : ℝ) := by
  have hc : Summable (fun n : ℕ => ((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_mul] using etaPlus_vonMangoldt_complex_summable x hx
  have he := coefficient_square_summable _ hc
  have hw : Summable (fun n : ℕ => if IsPrimePow n ∧ ¬Nat.Prime n then
      (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0) := by
    apply he.of_norm_bounded
    intro n
    split_ifs
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), etaPlus_coefficient_square]
    · simp only [norm_zero]
      exact sq_nonneg _
  have hm := (proper_prime_power_dirichlet_square_energy_summable.mul_left
    (18*x^(9/16 : ℝ)))
  calc
    _ ≤ ∑' n : ℕ, (18*x^(9/16 : ℝ))*(if IsPrimePow n ∧ ¬Nat.Prime n then
        (vonMangoldt n)^2*(n : ℝ)^(-(9/16 : ℝ)) else 0) := by
      apply hw.tsum_le_tsum ?_ hm
      intro n
      split_ifs with hn
      · have hs := etaPlus_scaled_square_envelope x hx n hn.1.pos
        nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (vonMangoldt n))]
      · simp
    _ = (18*x^(9/16 : ℝ))*(∑' n : ℕ, if IsPrimePow n ∧ ¬Nat.Prime n then
        (vonMangoldt n)^2*(n : ℝ)^(-(9/16 : ℝ)) else 0) := tsum_mul_left
    _ ≤ (18*x^(9/16 : ℝ))*7680 :=
      mul_le_mul_of_nonneg_left proper_prime_power_dirichlet_square_energy_le (by positivity)
    _ = _ := by ring

theorem etaPlus_prime_projection_error_le_reuse (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, ‖((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) -
      (if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then
        ((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) else 0)‖^2) ≤
      140000*x^(9/16 : ℝ) := by
  have hx0 : 0 < x := by linarith
  let c (n : ℕ) : ℂ := ((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ)
  have hc : Summable c := by
    simpa only [c, Complex.ofReal_mul] using etaPlus_vonMangoldt_complex_summable x hx0
  have he := coefficient_square_summable c hc
  let low (n : ℕ) : ℝ := if (n : ℝ) ≤ Real.sqrt x then
    (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0
  let pp (n : ℕ) : ℝ := if IsPrimePow n ∧ ¬Nat.Prime n then
    (vonMangoldt n)^2*(etaPlus ((n : ℝ)/x))^2 else 0
  have hl : Summable low := by
    apply he.of_norm_bounded
    intro n
    dsimp [low,c]
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), etaPlus_coefficient_square]
    · simp only [abs_zero]
      exact sq_nonneg _
  have hp : Summable pp := by
    apply he.of_norm_bounded
    intro n
    dsimp [pp,c]
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), etaPlus_coefficient_square]
    · simp only [abs_zero]
      exact sq_nonneg _
  have herr : Summable (fun n => ‖c n - (if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then c n else 0)‖^2) := by
    apply he.of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    split_ifs <;> simp
  have hpoint (n : ℕ) :
      ‖c n-(if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then c n else 0)‖^2 ≤ low n+pp n := by
    by_cases hn : Nat.Prime n ∧ Real.sqrt x < (n : ℝ)
    · simp only [if_pos hn,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
      dsimp [low,pp]
      split_ifs <;> positivity
    · rw [if_neg hn, sub_zero]
      dsimp [c,low,pp]
      rw [etaPlus_coefficient_square]
      by_cases hsmall : (n : ℝ) ≤ Real.sqrt x
      · rw [if_pos hsmall]
        apply le_add_of_nonneg_right
        split_ifs <;> positivity
      · rw [if_neg hsmall]
        have hnp : ¬Nat.Prime n := fun hp => hn ⟨hp,lt_of_not_ge hsmall⟩
        by_cases hpp : IsPrimePow n
        · rw [if_pos ⟨hpp,hnp⟩]
          simp
        · rw [if_neg (by tauto),vonMangoldt_eq_zero_iff.mpr hpp]
          simp
  change (∑' n : ℕ, ‖c n-(if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then c n else 0)‖^2) ≤ _
  calc
    _ ≤ ∑' n : ℕ, (low n+pp n) := herr.tsum_le_tsum hpoint (hl.add hp)
    _ = (∑' n : ℕ, low n)+(∑' n : ℕ, pp n) := hl.tsum_add hp
    _ ≤ 100*x^(9/16 : ℝ)+138240*x^(9/16 : ℝ) :=
      add_le_add (etaPlus_small_indices_square_energy_le x hx)
        (etaPlus_proper_prime_power_square_energy_le x hx0)
    _ ≤ 140000*x^(9/16 : ℝ) := by nlinarith [Real.rpow_nonneg hx0.le (9/16 : ℝ)]

end Helfgott

end

open MeasureTheory Finset ArithmeticFunction Helfgott
open scoped BigOperators Classical

theorem solution (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, ‖((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) -
      (if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then
        ((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) else 0)‖^2) ≤
      140000*x^(9/16 : ℝ) := Helfgott.etaPlus_prime_projection_error_le_reuse x hx

#print axioms solution
