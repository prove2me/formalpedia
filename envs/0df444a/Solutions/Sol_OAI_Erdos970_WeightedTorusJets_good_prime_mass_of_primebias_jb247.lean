-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.good_prime_mass_of_primebias_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:55.012296+00:00
-- url     : https://prove2.me/submissions/b1f4cb78-eb0c-4ab6-9fb8-05f7d1d455bf

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J005

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_E
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section

open _root_.Complex _root_.Filter
open scoped Topology ComplexConjugate

namespace RealCharacterAnalysis

theorem real_values_iff_quadratic {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ a : ZMod q, (χ a).im = 0) ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hc : star χ = χ := by
      ext a
      exact Complex.conj_eq_iff_im.mpr (h a)
    have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hc
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ * χ := sq χ
      _ = χ * χ⁻¹ := congrArg (χ * ·) hi.symm
      _ = 1 := mul_inv_cancel χ
  · intro h a
    rcases h a with h | h | h <;> simp [h]

theorem apply_prime_eq_zero_iff {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) : χ (p : ZMod q) = 0 ↔ p ∣ q := by
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_prime_iff_not_dvd hp, not_not]

end RealCharacterAnalysis
end
section

/-
Generated attribution header: the source file did not contain a copyright header.
The Mertens estimates in the following namespace are adapted from PrimeNumberTheoremAnd.IEANTN.Mertens.
Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
License: Apache License 2.0.

This code has been modified.
-/

namespace WeightedTorusJets.Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics Topology
open _root_.ArithmeticFunction hiding log

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all <;> linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all <;> linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast <;> linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem prime_log_div_bounded_error :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  refine ⟨log 4 + 6 + E₁, by positivity [E₁.nonneg], fun x hx => ?_⟩
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ log 4 + 6 + E₁
  have hlog : 0 ≤ log 4 := by positivity
  exact abs_le.mpr
    ⟨by linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx],
     by linarith [E₁Λ.le hx, E₁p.le_E₁Λ x, E₁.nonneg]⟩

end WeightedTorusJets.Mertens

end

end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SumLogPrimeFactors
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section

open scoped BigOperators

namespace WeightedTorusJets

theorem sum_log_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp : ∀ p ∈ q.primeFactors, 0 < (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (Finset.prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

theorem sum_log_div_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum fun p hp => ?_).trans (sum_log_primeFactors_le q)
  have hp1 : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_le
  exact div_le_self (Real.log_nonneg hp1) hp1

theorem sum_log_div_filter_dvd_le (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s with p ∣ q, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
    (sum_log_div_primeFactors_le q)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hpq⟩
    exact Nat.mem_primeFactors.mpr ⟨hprime p hps, hpq, hq⟩
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem sum_log_div_filter_le_cutoff (s : Finset ℕ) (H : ℕ) :
    ∑ p ∈ s with p ≤ H, Real.log p / p ≤
      ∑ p ∈ Finset.range (H + 1), Real.log p / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

end WeightedTorusJets
end
section

open scoped BigOperators

namespace WeightedTorusJets

theorem prime_mass_partition_le {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1) :
    ∑ p ∈ s, Real.log p / p ≤
      (∑ p ∈ s with c p = 1, Real.log p / p) +
      (∑ p ∈ s with p ∣ q, Real.log p / p) +
      (∑ p ∈ s with p ≤ H, Real.log p / p) +
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hn : 0 ≤ Real.log p / p := by
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast (hprime p hp).one_lt.le
  by_cases hsmall : p ≤ H
  · simp only [hsmall, ite_true, if_true]
    split_ifs <;> linarith
  have hlarge : H < p := lt_of_not_ge hsmall
  rcases hclass p hp with hpos | hram | hneg
  · simp only [hpos, ite_true, if_true]
    split_ifs <;> linarith
  · simp only [hram, ite_true, if_true]
    split_ifs <;> linarith
  · by_cases hram : p ∣ q
    · simp only [hram, ite_true, if_true]
      split_ifs <;> linarith
    have htwo : ¬ p ∣ 2 := by
      intro hp2
      have := Nat.le_of_dvd (by decide : 0 < 2) hp2
      omega
    simp only [hsmall, hram, hneg, hlarge, (hprime p hp).not_dvd_mul htwo hram,
      ite_false, if_false, ite_true, if_true, and_self, not_false_eq_true]
    split_ifs <;> linarith

theorem good_mass_of_estimates {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1)
    {L ell E A B D CH : ℝ} (hell : 0 ≤ ell) (hE : 0 ≤ E)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htotal : L - D ≤ ∑ p ∈ s, Real.log p / p)
    (hpositive : (∑ p ∈ s with c p = 1, Real.log p / p) ≤ A * ell + B * E)
    (hramified : (∑ p ∈ s with p ∣ q, Real.log p / p) ≤ ell)
    (hsmall : (∑ p ∈ s with p ≤ H, Real.log p / p) ≤ CH) :
    L - (A + B + 1) * ell - (A + B + 1) * E - (D + CH) ≤
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  have hpartition := prime_mass_partition_le hH s c hprime hclass
  nlinarith [mul_nonneg hB hell, mul_nonneg hA hE]

end WeightedTorusJets
end
section
namespace WeightedTorusJets

theorem good_prime_mass_of_primebias_jb247_oai {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      (∀ a : ZMod q, (χ a).im = 0) → ∀ X δ : ℝ, 3 ≤ X → 0 ≤ δ →
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        A * Real.log q + B * (δ * (Real.log X) ^ 2 / Real.log q) →
      Real.log X - C * Real.log q - C * (δ * (Real.log X) ^ 2 / Real.log q) - CH ≤
        ∑ p ∈ Nat.primesLE ⌊X⌋₊ with
          H < p ∧ ¬ p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p := by
  classical
  obtain ⟨D, _, hD⟩ := Mertens.prime_log_div_bounded_error
  refine ⟨A + B + 1, by linarith, fun H hH =>
    ⟨D + ∑ p ∈ Finset.range (H + 1), Real.log p / p, ?_⟩⟩
  intro q _ hq χ hreal X δ hX hδ hbias
  have hprime : ∀ p ∈ Nat.primesLE ⌊X⌋₊, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hquadratic := (RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal
  have hclass : ∀ p ∈ Nat.primesLE ⌊X⌋₊,
      χ ((p : ℕ) : ZMod q) = 1 ∨ p ∣ q ∨ χ ((p : ℕ) : ZMod q) = -1 := by
    intro p hp
    rcases hquadratic ((p : ℕ) : ZMod q) with hz | ho | hm
    · exact Or.inr (Or.inl ((RealCharacterAnalysis.apply_prime_eq_zero_iff χ
        (hprime p hp)).mp hz))
    · exact Or.inl ho
    · exact Or.inr (Or.inr hm)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hE : 0 ≤ δ * (Real.log X) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg hδ (sq_nonneg _)) hlogq
  have htotal : Real.log X - D ≤
      ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p := by
    have := (abs_le.mp (hD X (by linarith))).1
    linarith
  exact good_mass_of_estimates hH (Nat.primesLE ⌊X⌋₊) (fun p => χ ((p : ℕ) : ZMod q))
    hprime hclass hlogq hE hA hB htotal hbias
    (sum_log_div_filter_dvd_le q (by omega) _ hprime)
    (sum_log_div_filter_le_cutoff _ H)

end WeightedTorusJets
end

end AnalyticAssemblyScope

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.WeightedTorusJets.good_prime_mass_of_primebias_jb247_oai := @OAI.Erdos970.WeightedTorusJets.good_prime_mass_of_primebias_jb247_oai
