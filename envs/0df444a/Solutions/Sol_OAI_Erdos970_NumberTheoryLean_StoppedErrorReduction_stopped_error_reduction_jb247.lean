-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:09:02.74558+00:00
-- url     : https://prove2.me/submissions/5966fbfc-2cad-4378-9ff9-b3bd56f7af17

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_ReferenceCountEnvelope_reference_count_envelope_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RetainedOccupationLimit_retained_original_occupation_limit_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_ScaledOriginalTail_actual_uniform_scaled_tail_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceProductsBasics.availablePrimes_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure

lemma prefixWeight_sort (s : Finset ℕ) :
    prefixWeight (s.sort (· ≥ ·)) = ∏ p ∈ s, (p : ℝ)⁻¹ := by
  have h := List.prod_toFinset (fun p : ℕ => (p : ℝ)⁻¹) (s.sort_nodup (· ≥ ·))
  simpa only [Finset.sort_toFinset, prefixWeight] using h.symm

lemma sum_prefixWeights (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, prefixWeight l) = ∏ p ∈ s, (1 + (p : ℝ)⁻¹) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · simp_rw [prefixWeight_sort]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    have h' := congrArg List.toFinset h
    simpa only [Finset.sort_toFinset] using h'

lemma prefix_mass_le_exp (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, prefixWeight l) ≤ Real.exp (∑ p ∈ s, (p : ℝ)⁻¹) := by
  rw [sum_prefixWeights, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (p : ℝ)⁻¹

lemma sum_primesBetween {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ primesBetween a b, (p : ℝ)⁻¹) = reciprocalPrimes a b := by
  rw [primesBetween, Finset.sum_filter]
  exact (reciprocal_eq_core ha hab).symm

lemma interval_open_closed {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    intervalSum false true a b = reciprocalPrimes a b := by
  classical
  rw [intervalSum, reciprocal_eq_core ha hab]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha hab)).mp (Nat.mem_primesLE.mp hp).1
  simp [intervalGuard, hpb]

theorem total_prime_prefix_mass : ∃ M w₀ : ℝ, 0 < M ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, 1 ≤ ell → ell ≤ B →
      (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) ≤ M * B / ell := by
  obtain ⟨c, C, w₀, hc, hC, hw₀, h⟩ := harmonic_prime_measure
  refine ⟨Real.exp C, w₀, Real.exp_pos C, hw₀, ?_⟩
  intro w hw ell B hell hB
  have hw1 := lt_of_lt_of_le hw₀ hw
  have hwpos : 0 < w := lt_trans zero_lt_one hw1
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hBpos : 0 < B := lt_of_lt_of_le hellpos hB
  have hab : w ^ ell ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have ha : 0 ≤ w ^ ell := (Real.rpow_pos_of_pos hwpos ell).le
  have hh := h w hw ell B (by linarith) hB false true
  rw [harmonicMass_eq_intervalSum hw1, interval_open_closed ha hab] at hh
  have hexp : Real.exp (-c * Real.sqrt (ell * Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hs : reciprocalPrimes (w ^ ell) (w ^ B) ≤ Real.log B - Real.log ell + C := by
    have hu := (abs_le.mp hh).2
    have he := mul_le_mul_of_nonneg_left hexp hC.le
    linarith
  calc
    _ ≤ Real.exp (∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) := prefix_mass_le_exp _
    _ ≤ Real.exp (Real.log B - Real.log ell + C) := by
      apply Real.exp_le_exp.mpr
      simpa only [sum_primesBetween ha hab] using hs
    _ = Real.exp C * B / ell := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hBpos, Real.exp_log hellpos]
      ring

end ErdosPrimeInputs.PrimePrefixMass



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

lemma tilted_weight (l : List ℕ) :
    ((l.map (fun p : ℕ => 2 * (p : ℝ)⁻¹)).prod) = (2 : ℝ) ^ l.length * prefixWeight l := by
  induction l with
  | nil => simp [prefixWeight]
  | cons p l ih => simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, prefixWeight] at ih ⊢; rw [ih]; ring

lemma sum_sorted_products (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ decreasingPrefixes s, (l.map f).prod) = ∏ p ∈ s, (1 + f p) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · have hp (t : Finset ℕ) : ((t.sort (· ≥ ·)).map f).prod = ∏ p ∈ t, f p := by
      simpa only [Finset.sort_toFinset] using (List.prod_toFinset f (t.sort_nodup (· ≥ ·))).symm
    simp_rw [hp]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h

lemma sum_tilted_weights (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l) =
      ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := by
  simp_rw [← tilted_weight]
  exact sum_sorted_products s _

theorem longPrefixMass_le (s : Finset ℕ) (m : ℕ) :
    longPrefixMass s m ≤ Real.exp (2 * ∑ p ∈ s, (p : ℝ)⁻¹) / (2 : ℝ) ^ m := by
  apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)).mpr
  rw [mul_comm, longPrefixMass, Finset.mul_sum]
  calc
    _ ≤ ∑ l ∈ (decreasingPrefixes s).filter (fun l => m ≤ l.length),
        (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.mem_filter.mp hl).2) (prefixWeight_nonneg l)
    _ ≤ ∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro l hl hnot
      exact mul_nonneg (pow_nonneg (by norm_num) _) (prefixWeight_nonneg l)
    _ = ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := sum_tilted_weights s
    _ ≤ ∏ p ∈ s, Real.exp (2 * (p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (2 * (p : ℝ)⁻¹)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

end ErdosPrimeInputs.PrimePrefixTail



namespace ErdosPrimeInputs.LongPrimePaths

open _root_.Filter _root_.Asymptotics
open scoped Topology
open PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure PrimePrefixMass PrimePrefixTail

lemma fixed_tilt_tail (C A : ℝ) : ∀ᶠ B : ℝ in atTop, ∀ m : ℕ,
    (Real.log B) ^ 2 / 2 ≤ m →
      Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m ≤ B ^ (-A) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 * (A + 2 + 2 * |C|) / Real.log 2)))] with B hB hL
  intro m hm
  have hb0 : 0 < B := lt_trans zero_lt_one hB
  have hl1 : 1 ≤ Real.log B := le_trans (le_max_left _ _) hL
  have hl0 : 0 ≤ Real.log B := le_trans zero_le_one hl1
  have ht : 2 * (A + 2 + 2 * |C|) ≤ Real.log B * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (le_trans (le_max_right _ _) hL)
  have ht' := mul_le_mul_of_nonneg_right ht hl0
  have hm' := mul_le_mul_of_nonneg_right hm hlog2.le
  have hC' := mul_le_mul_of_nonneg_left hl1 (abs_nonneg C)
  have he : 2 * (Real.log B + C) - (m : ℝ) * Real.log 2 ≤ Real.log B * (-A) := by
    nlinarith [le_abs_self C]
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.exp_sub, Real.rpow_def_of_pos hb0]
  exact Real.exp_le_exp.mpr he

theorem long_prime_paths_superpolynomial : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ A : ℝ, ∀ᶠ B : ℝ in atTop, ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ,
      1 ≤ ell → ell ≤ B → ∀ m : ℕ, (Real.log B) ^ 2 / 2 ≤ m →
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) m ≤ B ^ (-A) := by
  obtain ⟨c, C, w₀, hc, hC, hw₀, h⟩ := harmonic_prime_measure
  refine ⟨w₀, hw₀, ?_⟩
  intro A
  filter_upwards [fixed_tilt_tail C A] with B htail
  intro w hw ell hell hB m hm
  have hw1 := lt_of_lt_of_le hw₀ hw
  have hwpos : 0 < w := lt_trans zero_lt_one hw1
  have hab : w ^ ell ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have ha : 0 ≤ w ^ ell := (Real.rpow_pos_of_pos hwpos ell).le
  have hh := h w hw ell B (by linarith) hB false true
  rw [harmonicMass_eq_intervalSum hw1, interval_open_closed ha hab] at hh
  have hexp : Real.exp (-c * Real.sqrt (ell * Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hsum : (∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) ≤ Real.log B + C := by
    rw [sum_primesBetween ha hab]
    have hu := (abs_le.mp hh).2
    have he := mul_le_mul_of_nonneg_left hexp hC.le
    have hl := Real.log_nonneg hell
    linarith
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) / (2 : ℝ) ^ m := longPrefixMass_le _ _
    _ ≤ Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by positivity)
    _ ≤ _ := htail m hm

end ErdosPrimeInputs.LongPrimePaths



namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset
open HarmonicPrimeMeasure PrimePrefixMass

lemma remainingGap_append (r₀ w : ℝ) (pre suf : List ℕ) :
    remainingGap r₀ w (pre ++ suf) = remainingGap (remainingGap r₀ w pre) w suf := by
  simp only [remainingGap, List.map_append, List.sum_append]
  ring

lemma cutoff_lower (x : ℕ → ℝ) {ell B : ℝ} (hB : ell ≤ B) (l : List ℕ)
    (hl : ∀ p ∈ l, ell ≤ x p) : ell ≤ cutoff x B l := by
  induction l generalizing B with
  | nil => exact hB
  | cons p l ih =>
    exact ih (hl p (by simp)) (fun q hq => hl q (by simp [hq]))

lemma suffix_le_cutoff (x : ℕ → ℝ) (hx : Monotone x) (B : ℝ) (pre suf : List ℕ)
    (hdec : (pre ++ suf).Pairwise (· > ·))
    (hB : ∀ p ∈ pre ++ suf, x p ≤ B) :
    ∀ p ∈ suf, x p ≤ cutoff x B pre := by
  induction pre generalizing B with
  | nil => exact hB
  | cons q pre ih =>
    have hp := List.pairwise_cons.mp hdec
    apply ih (x q) hp.2
    intro p hmem
    exact hx (le_of_lt (hp.1 p hmem))

lemma sum_exponents_le (x : ℕ → ℝ) (l : List ℕ) (b : ℝ)
    (hl : ∀ p ∈ l, x p ≤ b) : (l.map x).sum ≤ (l.length : ℝ) * b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have ht := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma prime_exponent_bounds {w ell B : ℝ} (hw : 1 < w) {p : ℕ}
    (hp : p ∈ primesBetween (w ^ ell) (w ^ B)) :
    ell < primeExponent w p ∧ primeExponent w p ≤ B := by
  obtain ⟨hp, hlow⟩ := Finset.mem_filter.mp hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hhigh : (p : ℝ) ≤ w ^ B :=
    (Nat.le_floor_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) B).le).mp (Nat.mem_primesLE.mp hp).1
  exact ⟨(lt_exponent_iff hw hp0).mpr hlow, (exponent_le_iff hw hp0).mpr hhigh⟩

theorem high_short_gap {r₀ w B ell S : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) {l : List ℕ}
    (hl : l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)))
    (hhigh : hasHighState r₀ w B S l) (hshort : (l.length : ℝ) < S / 2) :
    S * ell / 2 < remainingGap r₀ w l := by
  obtain ⟨pre, suf, rfl, hh⟩ := hhigh
  obtain ⟨hdec, hmem⟩ := mem_decreasingPrefixes.mp hl
  have hB : ∀ p ∈ pre ++ suf, primeExponent w p ≤ B := fun p hp =>
    (prime_exponent_bounds hw (hmem p hp)).2
  have hlow : ∀ p ∈ pre, ell ≤ primeExponent w p := fun p hp =>
    (prime_exponent_bounds hw (hmem p (List.mem_append_left _ hp))).1.le
  have hb : ell ≤ primeCutoff w B pre := cutoff_lower (primeExponent w) hellB pre hlow
  have hb0 : 0 < primeCutoff w B pre := lt_of_lt_of_le hell hb
  have hcut := suffix_le_cutoff (primeExponent w) (exponent_monotone hw) B pre suf hdec hB
  have hsum := sum_exponents_le (primeExponent w) suf (primeCutoff w B pre) hcut
  have hlen : (suf.length : ℝ) ≤ (List.length (pre ++ suf) : ℝ) := by
    simp only [List.length_append, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) pre.length]
  have hmul := mul_le_mul_of_nonneg_right hlen hb0.le
  have hshortmul := mul_lt_mul_of_pos_right hshort hb0
  have hbase := mul_le_mul_of_nonneg_left hb hS
  have hh := (lt_div_iff₀ hb0).mp hh
  rw [remainingGap_append]
  unfold remainingGap
  change S * primeCutoff w B pre < r₀ - (pre.map (primeExponent w)).sum at hh
  nlinarith

end ErdosPrimeInputs.HighPrimeGeometry



namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset
open PrimePrefixMass PrimePrefixTail HighPrimeGeometry

theorem rewardedHighMass_le {r₀ w B ell S c : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hc : 0 < c) :
    rewardedHighMass r₀ w B ell S c ≤
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈S / 2⌉₊ +
      (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) *
        Real.exp (-c * (S * ell / 2)) := by
  classical
  simp only [rewardedHighMass, longPrefixMass, Finset.sum_filter]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l hl
  have hwgt := prefixWeight_nonneg l
  have he := (Real.exp_pos (-c * (S * ell / 2))).le
  by_cases hcond : hasHighState r₀ w B S l ∧ 0 ≤ remainingGap r₀ w l
  · rw [ite_eq_left hcond]
    by_cases hlong : ⌈S / 2⌉₊ ≤ l.length
    · rw [ite_eq_left hlong]
      have hexp : Real.exp (-c * remainingGap r₀ w l) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hcond.2)
      have hmul := mul_le_mul_of_nonneg_left hexp hwgt
      have hn := mul_nonneg hwgt he
      linarith
    · rw [ite_eq_right hlong, zero_add]
      have hshort : (l.length : ℝ) < S / 2 := Nat.lt_ceil.mp (lt_of_not_ge hlong)
      have hgap := high_short_gap hw hell hellB hS hl hcond.1 hshort
      apply mul_le_mul_of_nonneg_left _ hwgt
      apply Real.exp_le_exp.mpr
      nlinarith
  · rw [ite_eq_right hcond]
    apply add_nonneg
    · split_ifs <;> positivity
    · exact mul_nonneg hwgt he

end ErdosPrimeInputs.HighPrimeMass



namespace ErdosPrimeInputs.HighPrimeRemoval

open _root_.Filter _root_.Asymptotics
open scoped Topology
open PrimePrefixMass PrimePrefixTail LongPrimePaths HighPrimeGeometry HighPrimeMass

lemma large_gap_saving {c : ℝ} (hc : 0 < c) (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    B * Real.exp (-c * ((Real.log B) ^ 2 / 2)) ≤ B ^ (-A) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 * (A + 1) / c)))] with B hB hL
  have hb0 : 0 < B := lt_trans zero_lt_one hB
  have hl0 : 0 ≤ Real.log B := le_trans zero_le_one (le_trans (le_max_left _ _) hL)
  have ht : 2 * (A + 1) ≤ Real.log B * c :=
    (div_le_iff₀ hc).mp (le_trans (le_max_right _ _) hL)
  have hm := mul_le_mul_of_nonneg_right ht hl0
  have he : Real.log B + (-c * ((Real.log B) ^ 2 / 2)) ≤ Real.log B * (-A) := by nlinarith
  calc
    _ = Real.exp (Real.log B + (-c * ((Real.log B) ^ 2 / 2))) := by
      rw [Real.exp_add, Real.exp_log hb0]
    _ ≤ Real.exp (Real.log B * (-A)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hb0 (-A)).symm

theorem rewarded_high_removal : ∃ M w₀ : ℝ, 0 < M ∧ 1 < w₀ ∧
    ∀ c : ℝ, 0 < c → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ r₀ : ℝ,
        rewardedHighMass r₀ w B ell ((Real.log B) ^ 2) c ≤ M * B ^ (-A) := by
  obtain ⟨M, wMass, hM, hwMass, hmass⟩ := total_prime_prefix_mass
  obtain ⟨wTail, hwTail, htail⟩ := long_prime_paths_superpolynomial
  refine ⟨1 + M, max wMass wTail, by positivity, lt_of_lt_of_le hwMass (le_max_left _ _), ?_⟩
  intro c hc A
  filter_upwards [htail A, large_gap_saving hc A] with B htailB hrewardB
  intro w hw ell hell hellB r₀
  have hwM : wMass ≤ w := le_trans (le_max_left _ _) hw
  have hwT : wTail ≤ w := le_trans (le_max_right _ _) hw
  have hw1 : 1 < w := lt_of_lt_of_le hwMass hwM
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hB0 : 0 < B := lt_of_lt_of_le hell0 hellB
  have hmassB : (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) ≤ M * B :=
    (hmass w hwM ell B hell hellB).trans (div_le_self (mul_nonneg hM.le hB0.le) hell)
  have hE : Real.exp (-c * ((Real.log B) ^ 2 * ell / 2)) ≤
      Real.exp (-c * ((Real.log B) ^ 2 / 2)) := by
    have hp := mul_le_mul_of_nonneg_left hell (sq_nonneg (Real.log B))
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈(Real.log B) ^ 2 / 2⌉₊ +
        (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) *
          Real.exp (-c * ((Real.log B) ^ 2 * ell / 2)) :=
      rewardedHighMass_le hw1 hell0 hellB (sq_nonneg _) hc
    _ ≤ B ^ (-A) + (M * B) * Real.exp (-c * ((Real.log B) ^ 2 / 2)) := by
      apply add_le_add
      · exact htailB w hwT ell hell hellB _ (Nat.le_ceil _)
      · exact mul_le_mul hmassB hE (Real.exp_pos _).le (mul_nonneg hM.le hB0.le)
    _ ≤ B ^ (-A) + M * B ^ (-A) := by
      apply add_le_add le_rfl
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hrewardB hM.le
    _ = (1 + M) * B ^ (-A) := by ring

end ErdosPrimeInputs.HighPrimeRemoval


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem valid_final {i : Side} {s : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) : Valid (finalSide i ts) (finalRatio s ts) := by
  induction ts generalizing i s with
  | nil => exact hs
  | cons t ts ih => exact ih (valid_next hs ht.1) ht.2

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

theorem finalGap_eq_cost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) :
    finalGap r ts = r * Real.exp (-pathCost ts) := by
  induction ts generalizing i s r with
  | nil => simp [finalGap, pathCost]
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    rw [finalGap, ih hv ht.2, nextGap_eq_cost (valid_pos hv), pathCost,
      neg_add, Real.exp_add]
    ring

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open _root_.Erdos970.Set
open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

theorem prime_tilt_step_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    (p : ℝ)⁻¹ = primeTilt w r i s p * ((r - primeExponent w p)/r)^2 *
      (weight i s / weight i.flip (childRatio w r p)) := by
  have ht := valid_pos (child_valid hs hp)
  have hw := weight_pos hs
  have hw' := weight_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  unfold primeTilt nextGap
  field_simp [hr.ne', ht.ne', hw.ne', hw'.ne']

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

theorem ratios_admissible {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : Admissible i s (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => trivial
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ⟨(Finset.mem_filter.mp hp).2.2.2.1, ih hps⟩

theorem primeFinalGap_eq {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = finalGap r (primeRatios w r ps) := by
  induction ps generalizing i s r cap closed with
  | nil => rfl
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    simp only [primeFinalGap, primeRatios, finalGap]
    rw [nextGap_childRatio hr (child_exponent_positive hell hp) (valid_pos (child_valid hs hp))]
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

theorem prime_prefix_weight_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = tiltProduct w i s r ps * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  induction ps generalizing i s r cap closed with
  | nil =>
    simp only [prefixWeight, List.map_nil, List.prod_nil, tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    rw [div_self hr.ne', div_self (weight_pos hs).ne']
    norm_num
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    have hr' := child_gap_positive hell hr hs hp
    have hs' := child_valid hs hp
    have hi := ih hr' hs' hps
    have hf := weight_pos (valid_final hs' (ratios_admissible hps))
    have hstep := prime_tilt_step_identity hell hr hs hp
    simp only [prefixWeight, List.map_cons, List.prod_cons] at ⊢
    change (p : ℝ)⁻¹ * prefixWeight ps = _
    rw [hi, hstep]
    simp only [tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    field_simp [hr.ne', hr'.ne', (weight_pos hs').ne', hf.ne']

theorem normalized_product_correction {e : ℝ} (he : 0 ≤ e) (w : ℝ) (i : Side) (s r : ℝ) (ps : List ℕ) :
    normalizedTiltProduct e w i s r ps * (1+e)^ps.length = tiltProduct w i s r ps := by
  induction ps generalizing i s r with
  | nil => simp [normalizedTiltProduct, tiltProduct]
  | cons p ps ih =>
    simp only [normalizedTiltProduct, tiltProduct, List.length_cons, pow_succ]
    rw [show (primeTilt w r i s p / (1+e)) * normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps *
      ((1+e)^ps.length * (1+e)) = primeTilt w r i s p *
        (normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps * (1+e)^ps.length) by
          field_simp [show 1+e ≠ 0 by linarith]]
    rw [ih]

theorem normalized_prime_prefix_weight_identity {w ell S s r cap e : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (he : 0 ≤ e) (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = normalizedTiltProduct e w i s r ps * (1+e)^ps.length * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  rw [normalized_product_correction he]
  exact prime_prefix_weight_identity hell hr hs hpath

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_gap_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = primeFinalGap w z.gap ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeFinalGap, step] using ih (step w z p)

theorem terminal_ratio_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).ratio = finalRatio z.ratio (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalRatio, step] using ih (step w z p)

theorem terminal_side_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = finalSide z.side (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalSide, step] using ih (step w z p)

end NumberTheoryLean.PrimeHistories

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PrefixCompletions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open ErdosPrimeInputs.PrimePrefixMass

theorem append_mem_decreasing_iff {P : Finset ℕ} {pre suf : List ℕ}
    (hpre : pre ∈ decreasingPrefixes P) :
    pre++suf ∈ decreasingPrefixes P ↔ suf ∈ decreasingPrefixes (suffixPrimes P pre) := by
  obtain ⟨hpp,hpm⟩ := mem_decreasingPrefixes.mp hpre
  constructor
  · intro h
    obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
    obtain ⟨_,hs,hcross⟩ := List.pairwise_append.mp hp
    apply mem_decreasingPrefixes.mpr
    refine ⟨hs,?_⟩
    intro q hq
    apply Finset.mem_filter.mpr
    exact ⟨hm q (List.mem_append.mpr (Or.inr hq)),fun p hp => hcross p hp q hq⟩
  · intro h
    obtain ⟨hs,hm⟩ := mem_decreasingPrefixes.mp h
    apply mem_decreasingPrefixes.mpr
    refine ⟨List.pairwise_append.mpr ⟨hpp,hs,?_⟩,?_⟩
    · intro p hp q hq
      exact (Finset.mem_filter.mp (hm q hq)).2 p hp
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hpm p hp
      · exact (Finset.mem_filter.mp (hm p hp)).1

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferencePrefixRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePrefixRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem singleton_prefix_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : [p] ∈ decreasingPrefixes P := by
  apply mem_decreasingPrefixes.mpr
  exact ⟨by simp,by intro q hq; simpa using List.mem_singleton.mp hq ▸ hp⟩

theorem nonempty_eq_first_completions (P : Finset ℕ) :
    nonemptyPrefixes P=P.biUnion (fun p => completions P [p]) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hpD,hne⟩ := Finset.mem_filter.mp hp
    cases ps with
    | nil => exact False.elim (hne rfl)
    | cons p ps =>
      have hpP : p ∈ P := (mem_decreasingPrefixes.mp hpD).2 p (by simp)
      have ht := (append_mem_decreasing_iff (singleton_prefix_mem hpP)).mp hpD
      exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨ps,ht,rfl⟩⟩
  · intro hp
    obtain ⟨p,hpP,hps⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨tail,htail,rfl⟩ := Finset.mem_image.mp hps
    exact Finset.mem_filter.mpr ⟨(append_mem_decreasing_iff (singleton_prefix_mem hpP)).mpr htail,by simp⟩

theorem first_completions_disjoint (P : Finset ℕ) :
    (P:Set ℕ).PairwiseDisjoint (fun p => completions P [p]) := by
  intro p _hp q _hq hne
  apply Finset.disjoint_left.mpr
  intro ps hp hq
  obtain ⟨sp,_hsp,he⟩ := Finset.mem_image.mp hp
  obtain ⟨sq,_hsq,hf⟩ := Finset.mem_image.mp hq
  have hh := he.trans hf.symm
  simp only [List.singleton_append] at hh
  exact hne (List.cons.inj hh).1

theorem sum_decreasing_by_first (P : Finset ℕ) (F : List ℕ → ℝ) :
    (∑ ps ∈ decreasingPrefixes P,F ps)=F []+
      ∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),F (p::ps) := by
  have he : (decreasingPrefixes P).filter (fun ps => ps=[])= {[]} := by
    ext ps
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst ps
      exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,rfl⟩
  have hs := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (fun ps => ps=[]) F
  rw [he,Finset.sum_singleton] at hs
  change F []+(∑ ps ∈ nonemptyPrefixes P,F ps)=(∑ ps ∈ decreasingPrefixes P,F ps) at hs
  rw [← hs,nonempty_eq_first_completions,Finset.sum_biUnion (first_completions_disjoint P)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold completions
  rw [Finset.sum_image]
  · have hsuf : suffixPrimes P [p]=P.filter (fun q => q<p) := by simp [suffixPrimes]
    rw [hsuf]
    apply Finset.sum_congr rfl
    intro ps _
    rfl
  · intro a _ b _ h
    exact List.append_cancel_left h

theorem reference_polynomial_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    referencePolynomial w P i r=1-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps else 0)
  have he : referencePolynomial w P i r =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps else 0 := by
    rw [referencePolynomial,referencePrefixes,Finset.sum_filter]
    rfl
  have hnil : (if admitted w i r [] then signedWeight [] else 0)=1 := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,referencePolynomial,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceCutoffRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceForestTelescoping

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffixPrimes_nil (P : Finset ℕ) : suffixPrimes P []=P := by simp [suffixPrimes]

theorem suffixPrimes_cons (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    suffixPrimes P (p::ps)=suffixPrimes (P.filter (fun q => q<p)) ps := by
  ext q
  simp [suffixPrimes,and_assoc,and_left_comm,and_comm]

end NumberTheoryLean.ReferenceForestTelescoping

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

variable (w ell S : ℝ) (start : Node)

variable {w ell S : ℝ} {start : Node}

theorem pathLaw_isProbability (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (n : ℕ) :
    IsProbabilityMeasure (pathLaw w ell S start n) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold pathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainProbabilities

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeKilledChain

variable {w ell S : ℝ} {start : Node}

theorem history_append_eq_iff (h k : History w ell S start) (p q : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (hq : q ∈ nodeChildren w ell S k.node) :
    h.append p hp = k.append q hq ↔ h = k ∧ p = q := by
  constructor
  · intro heq
    have hl := congrArg History.primes heq
    have hh := List.append_singleton_inj.mp hl
    exact ⟨History.ext hh.1,hh.2⟩
  · rintro ⟨rfl,rfl⟩
    exact History.ext rfl

theorem liveLaw_at_append (g h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    liveLaw w ell S start g {some (h.append p hp)} =
      ({h} : Set (History w ell S start)).indicator (fun _ => childProbability w ell S start h p) g := by
  classical
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Option.some.injEq, history_append_eq_iff,
    mul_ite, mul_one, mul_zero]
  by_cases hgh : g = h
  · subst g
    simp only [true_and, ite_true, if_true]
    calc
      _ = ∑ q ∈ nodeChildren w ell S h.node, if q = p then childProbability w ell S start h q else 0 :=
        Finset.sum_attach _ (fun q : ℕ => if q = p then childProbability w ell S start h q else 0)
      _ = _ := by simp [hp]
  · simp [hgh]

theorem chain_at_append (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (z : ChainState w ell S start) :
    chain w ell S start z {some (h.append p hp)} =
      ({some h} : Set (ChainState w ell S start)).indicator (fun _ => childProbability w ell S start h p) z := by
  classical
  cases z with
  | none => simp [chain_none, Set.indicator]
  | some g =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_at_append, Measure.smul_apply]
    simp [Set.indicator]

theorem pathLaw_append (n : ℕ) (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    pathLaw w ell S start (n+1) {some (h.append p hp)} =
      childProbability w ell S start h p * pathLaw w ell S start n {some h} := by
  unfold pathLaw
  have hpow : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  rw [hpow, Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
  calc
    _ = ∫⁻ z, ({some h} : Set (ChainState w ell S start)).indicator
        (fun _ => childProbability w ell S start h p) z ∂((chain w ell S start)^n) (some History.empty) :=
      lintegral_congr (fun z => chain_at_append h p hp z)
    _ = _ := by rw [lintegral_indicator (measurableSet_singleton _), lintegral_const, Measure.restrict_apply_univ]

theorem nodeProduct_append (e w : ℝ) (z : Node) (ps qs : List ℕ) :
    nodeProduct e w z (ps++qs) = nodeProduct e w z ps * nodeProduct e w (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp [nodeProduct, normalizedTiltProduct, terminal]
  | cons p ps ih =>
    change (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) (ps++qs) =
      ((primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps) *
        nodeProduct e w (terminal w (step w z p) ps) qs
    rw [ih, mul_assoc]

theorem nodeProduct_nonnegative {e : ℝ} (he : 0 ≤ e) {z : Node} {ps : List ℕ}
    (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) : 0 ≤ nodeProduct e w z ps := by
  induction ps generalizing z with
  | nil => exact zero_le_one
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hrest⟩
    change 0 ≤ (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps
    exact mul_nonneg (div_nonneg (primeTilt_nonneg hs hchild) (by linarith)) (ih (child_valid hs hchild) hrest)

theorem pathLaw_singleton_weight (hs : Valid start.side start.ratio) (h : History w ell S start) :
    pathLaw w ell S start h.primes.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start h.primes) := by
  classical
  have main : ∀ ps : List ℕ, ∀ h : History w ell S start, h.primes = ps →
      pathLaw w ell S start ps.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start ps) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil =>
      intro h heq
      have hh : h = History.empty := History.ext heq
      subst h
      change Measure.dirac (some (History.empty : History w ell S start)) {some History.empty} = ENNReal.ofReal (1 : ℝ)
      simp
    | append_singleton ps p ih =>
      intro h heq
      have hall : allowed w ell S start (ps++[p]) := heq ▸ h.admissible
      obtain ⟨hpre,hlast⟩ := (allowed_append w ell S start ps [p]).mp hall
      let g : History w ell S start := ⟨ps,hpre⟩
      have hp : p ∈ nodeChildren w ell S g.node := (allowed_cons w ell S g.node p []).mp hlast |>.1
      have hh : h = g.append p hp := History.ext heq
      rw [hh, List.length_append, List.length_singleton, pathLaw_append, ih g rfl, nodeProduct_append]
      have hgn : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
      have hn : 0 ≤ primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) :=
        div_nonneg (primeTilt_nonneg (w := w) (r := g.node.gap) (i := g.node.side) (s := g.node.ratio) hgn hp) (normalizer_pos w).le
      change ENNReal.ofReal (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w)) *
          ENNReal.ofReal (nodeProduct (epsilon w) w start ps) =
        ENNReal.ofReal (nodeProduct (epsilon w) w start ps *
          (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) * 1))
      rw [← ENNReal.ofReal_mul hn]
      congr 1
      ring
  exact main h.primes h rfl

theorem source_prime_weight_identity (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal * (1+epsilon w)^h.primes.length *
        (h.node.gap/start.gap)^2 * (weight start.side start.ratio / weight h.node.side h.node.ratio) := by
  rw [pathLaw_singleton_weight hs h, ENNReal.toReal_ofReal (nodeProduct_nonnegative (epsilon_pos w).le hs h.admissible)]
  have hweight := normalized_prime_prefix_weight_identity (epsilon_pos w).le hell hr hs h.admissible
  simpa only [nodeProduct, History.node, terminal_gap_eq, terminal_side_eq, terminal_ratio_eq] using hweight

end NumberTheoryLean.PrimeChainProbabilities



namespace NumberTheoryLean.PrimeHistoryHorizon

open _root_.Set _root_.Finset
open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem valid_ratio_lower {i : Side} {t : ℝ} (ht : Valid i t) : (19/20 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem prime_cost_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hs : Valid i s) (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    (ps.length : ℝ)/(S+1) ≤ pathCost (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => simp [primeRatios,pathCost]
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    have ht := valid_pos (child_valid hs hp)
    have htS : childRatio w r p ≤ S := (Finset.mem_filter.mp hp).2.2.2.2
    have hc : 1/(S+1) ≤ cost (childRatio w r p) :=
      (one_div_le_one_div_of_le (by linarith : 0 < childRatio w r p+1) (by linarith)).trans
        (cost_ge_inv_add_one ht)
    have hih := ih (child_valid hs hp) hrest
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_div, primeRatios, pathCost]
    linarith

theorem prime_gap_cost {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = r * Real.exp (-pathCost (primeRatios w r ps)) := by
  rw [primeFinalGap_eq hell hr hs hpath, finalGap_eq_cost hs (ratios_admissible hpath)]

theorem prime_final_gap_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hne : ps ≠ []) :
    (19/20 : ℝ)*ell < primeFinalGap w r ps := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    cases ps with
    | nil =>
      have hx : ell < primeExponent w p := (Finset.mem_filter.mp hp).2.1
      have hx0 : 0 < primeExponent w p := hell.trans hx
      have ht := valid_ratio_lower (child_valid hs hp)
      have heq : r-primeExponent w p = childRatio w r p * primeExponent w p := by
        unfold childRatio
        field_simp
      change (19/20 : ℝ)*ell < r-primeExponent w p
      calc
        _ < (19/20 : ℝ)*primeExponent w p := mul_lt_mul_of_pos_left hx (by norm_num)
        _ ≤ childRatio w r p * primeExponent w p := mul_le_mul_of_nonneg_right ht hx0.le
        _ = _ := heq.symm
    | cons q qs =>
      exact ih (child_gap_positive hell.le hr hs hp) (child_valid hs hp) hrest (by simp)

theorem prime_source_horizon {w ell S s r cap B : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hB : 0 < B) (hsize : r ≤ (23/10 : ℝ)*B) :
    ps.length < sourceHorizon S B := by
  by_cases hne : ps = []
  · subst ps
    unfold sourceHorizon
    simp
  · have hell0 : 0 < ell := by linarith
    have hgap := prime_final_gap_lower hell0 hr hs hpath hne
    have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19/20) hell0) hgap
    rw [prime_gap_cost hell0.le hr hs hpath,
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hc := prime_cost_lower hs hpath
    have hlogR := Real.log_le_log hr hsize
    rw [Real.log_mul (by norm_num : (23/10 : ℝ) ≠ 0) hB.ne'] at hlogR
    have hlog23 : Real.log (23/10 : ℝ) ≤ 13/10 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23/10)
      norm_num at h
      exact h
    have hlog19 : (-1/19 : ℝ) ≤ Real.log (19/20 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/20)
      norm_num at h
      linarith
    have hlogell : Real.log (19/20 : ℝ) ≤ Real.log ((19/20 : ℝ)*ell) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hn : (ps.length : ℝ)/(S+1) < Real.log B+2 := by linarith
    have hmul := (div_lt_iff₀ (by linarith : 0 < S+1)).mp hn
    have hceil := Nat.le_ceil ((S+1)*(Real.log B+2))
    have hreal : (ps.length : ℝ) < (sourceHorizon S B : ℝ) := by
      unfold sourceHorizon
      push_cast
      nlinarith
    exact_mod_cast hreal

theorem history_length_lt {w ell S B : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (h : History w ell S start) :
    h.primes.length < sourceHorizon S B :=
  prime_source_horizon hell hS hr hs h.admissible hB hsize

end NumberTheoryLean.PrimeHistoryHorizon



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeHistoryHorizon LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

end NumberTheoryLean.PrimeChainHorizon



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

theorem history_consistent {w ell S : ℝ} {start : Node} (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (h : History w ell S start) : Consistent h.node :=
  terminal_consistent hell hr hs hc h.admissible

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem terminal_gap_remaining (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = remainingGap z.gap w ps := by
  induction ps generalizing z with
  | nil => simp [remainingGap]
  | cons p ps ih =>
    rw [terminal_cons,ih]
    simp only [remainingGap,step,List.map_cons,List.sum_cons]
    ring

theorem terminal_cutoff (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).cutoff = primeCutoff w z.cutoff ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => exact ih (step w z p)

theorem terminal_ratio_remaining {w ell U : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    (terminal w z ps).ratio = remainingGap z.gap w ps / primeCutoff w z.cutoff ps := by
  have hc := terminal_consistent hell hr hs hz hp
  have hg := terminal_gap_positive hell hr hs hp
  have hv := valid_pos (terminal_valid hs hp)
  rw [← terminal_gap_remaining w z ps,← terminal_cutoff w z ps]
  change (terminal w z ps).cutoff = (terminal w z ps).gap/(terminal w z ps).ratio at hc
  rw [hc]
  field_simp

theorem actual_has_high_iff {w ell U T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  constructor <;> rintro ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [← terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem uncapped_gap_positive {w ell : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hp : uncappedAllowed w ell z ps) : 0 < (terminal w z ps).gap := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact terminal_gap_positive hell hr hs hU

theorem uncapped_has_high_iff {w ell T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hp : uncappedAllowed w ell z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact actual_has_high_iff hell hr hs hz hU

end NumberTheoryLean.ActualPrimeHigh

end

section

open scoped BigOperators
namespace NumberTheoryLean.ActualPrimeHigh
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HighPrimeGeometry

theorem uncapped_rewarded_mass_le {w ell : ℝ} (_hw : 1 < w) {z : Node}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (T c : ℝ) :
    uncappedRewardedHighMass w ell z T c ≤
      ErdosPrimeInputs.HighPrimeMass.rewardedHighMass z.gap w z.cutoff ell T c := by
  classical
  unfold uncappedRewardedHighMass ErdosPrimeInputs.HighPrimeMass.rewardedHighMass
  simp only [terminal_gap_remaining]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hfamily,hhigh⟩ := Finset.mem_filter.mp hp
    obtain ⟨hdec,hactual⟩ := Finset.mem_filter.mp hfamily
    have hgap := (uncapped_gap_positive hell hr hs hactual).le
    rw [terminal_gap_remaining] at hgap
    exact Finset.mem_filter.mpr ⟨hdec,
      (uncapped_has_high_iff hell hr hs hz hactual).mp hhigh,hgap⟩
  · intro ps _ _
    exact mul_nonneg (prefixWeight_nonneg ps) (Real.exp_pos _).le

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open FinitePathGeometry PrimeHistories PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ActualPrimeHigh

theorem sum_histories {w ell S : ℝ} (hw : 1 < w) (start : Node) (F : List ℕ → ℝ) :
    letI := historyFintype (ell := ell) (S := S) hw start
    (∑ h : History w ell S start,F h.primes) =
      ∑ ps ∈ retainedPrefixes w ell S start,F ps := by
  classical
  let := historyFintype (ell := ell) (S := S) hw start
  calc
    _ = ∑ ps : {ps // ps ∈ retainedPrefixes w ell S start},F ps.val :=
      (Equiv.sum_comp (retainedHistoryEquiv hw start) (fun h => F h.primes)).symm
    _ = _ := Finset.sum_attach _ F

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

theorem terminal_cutoff_lower {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hc : ell ≤ start.cutoff) (hp : allowed w ell S start ps) : ell ≤ (terminal w start ps).cutoff := by
  classical
  induction ps generalizing start with
  | nil => exact hc
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := (allowed_cons w ell S start p ps).mp hp
    have hlo : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
      (Finset.mem_filter.mp hchild).2.1
    exact ih hlo.le htail

theorem history_ratio_le_gap {w ell S : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (h : History w ell S start) :
    h.node.ratio ≤ h.node.gap := by
  have hv : 0 < h.node.ratio := valid_pos (terminal_valid hs h.admissible)
  have hn : Consistent h.node := history_consistent (by linarith) hr hs hc h
  have hlow : ell ≤ h.node.cutoff := terminal_cutoff_lower hcut h.admissible
  change h.node.cutoff = h.node.gap/h.node.ratio at hn
  have he := (eq_div_iff hv.ne').mp hn
  nlinarith

theorem scaledWeight_nonneg {w B ell S : ℝ} {start : Node}
    (hs : Valid start.side start.ratio) (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hφ := (weight_pos hs).le
    have hφ' := (weight_pos (terminal_valid hs h.admissible)).le
    have he := (normalizer_pos w).le
    unfold scaledWeight
    positivity

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferenceHistoryAdmission
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHistoryAdmission

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence ReferenceSourcePrimeSets
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem cap_lower_ratio {w : ℝ} {z : Node} {p : ℕ} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hx : 0 < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p)) :
    z.ratio-1 ≤ childRatio w z.gap p := by
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact h.le
    | true => simpa [capGuard,hcl] using hcap
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hm := mul_le_mul_of_nonneg_right hxp (valid_pos hs).le
  have hd : z.ratio ≤ z.gap/primeExponent w p := (le_div_iff₀ hx).mpr (by nlinarith)
  unfold childRatio
  linarith

end NumberTheoryLean.ReferenceHistoryAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedPrimeCongruence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]

omit [DecidableEq α] in

theorem exists_childCell {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α}
    (hx : x ∈ C) (hnot : x ∉ survivors C P bad) :
    ∃ p ∈ P, x ∈ childCell C P bad p := by
  classical
  have hbad : ∃ p ∈ P, bad p x := by
    by_contra h
    exact hnot (mem_survivors.mpr ⟨hx, fun p hp hpx => h ⟨p, hp, hpx⟩⟩)
  let B := P.filter fun p => bad p x
  have hB : B.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hbad
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpx⟩⟩
  let p := B.min' hB
  have hpB : p ∈ B := Finset.min'_mem B hB
  obtain ⟨hpP, hpx⟩ := Finset.mem_filter.mp hpB
  refine ⟨p, hpP, mem_childCell.mpr ⟨hx, hpx, ?_⟩⟩
  intro q hqP hqp hqx
  have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqP, hqx⟩
  exact (not_lt_of_ge (Finset.min'_le B q hqB)) hqp

omit [DecidableEq α] in

theorem childCell_disjoint {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {p q : ι}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    Disjoint (childCell C P bad p) (childCell C P bad q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨_, hpx, hpmin⟩ := mem_childCell.mp hxp
  obtain ⟨_, hqx, hqmin⟩ := mem_childCell.mp hxq
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · exact hqmin p hp hpq hpx
  · exact hpmin q hq hqp hqx

theorem biUnion_childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    P.biUnion (childCell C P bad) = C \ survivors C P bad := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxC, hpx, _⟩ := mem_childCell.mp hxp
    exact Finset.mem_sdiff.mpr ⟨hxC,
      fun hxs => (mem_survivors.mp hxs).2 p hp hpx⟩
  · intro hx
    obtain ⟨hxC, hxnot⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_biUnion.mpr (exists_childCell hxC hxnot)

theorem sum_card_childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    ∑ p ∈ P, (childCell C P bad p).card = (C \ survivors C P bad).card := by
  classical
  rw [← biUnion_childCell C P bad]
  symm
  exact Finset.card_biUnion fun p hp q hq hne => childCell_disjoint hp hq hne

theorem card_survivors_add_sum (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    (survivors C P bad).card + ∑ p ∈ P, (childCell C P bad p).card = C.card := by
  rw [sum_card_childCell, Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card fun _ hx => (mem_survivors.mp hx).1

theorem card_survivors_eq_sub_sum (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    ((survivors C P bad).card : ℤ) =
      (C.card : ℤ) - ∑ p ∈ P, ((childCell C P bad p).card : ℤ) := by
  have h : ((survivors C P bad).card : ℤ) +
      ∑ p ∈ P, ((childCell C P bad p).card : ℤ) = (C.card : ℤ) := by
    exact_mod_cast card_survivors_add_sum C P bad
  linarith

theorem residueCandidates_insert (Y : ℕ) (H small : Finset ℕ)
    (a : ℕ → ℕ) (p : ℕ) :
    residueCandidates Y (insert p H) small a =
      (residueCandidates Y H small a).filter (residueBad a p) := by
  classical
  ext n
  simp only [mem_residueCandidates, Finset.mem_filter, Finset.mem_insert,
    forall_eq_or_imp]
  tauto

theorem residue_childCell_eq (Y : ℕ) (H small P : Finset ℕ)
    (a : ℕ → ℕ) (p : ℕ) :
    childCell (residueCandidates Y H small a) P (residueBad a) p =
      survivors (residueCandidates Y (insert p H) small a)
        (P.filter fun q => q < p) (residueBad a) := by
  classical
  rw [residueCandidates_insert]
  ext n
  simp only [mem_childCell, mem_survivors, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hpn, hleast⟩
    exact ⟨⟨hn, hpn⟩, fun q hq => hleast q hq.1 hq.2⟩
  · rintro ⟨⟨hn, hpn⟩, hleast⟩
    exact ⟨hn, hpn, fun q hq hqp => hleast q ⟨hq, hqp⟩⟩

theorem residue_tree_identity (Y : ℕ) (H small P : Finset ℕ) (a : ℕ → ℕ) :
    ((survivors (residueCandidates Y H small a) P (residueBad a)).card : ℤ) =
      ((residueCandidates Y H small a).card : ℤ) -
        ∑ p ∈ P,
          ((survivors (residueCandidates Y (insert p H) small a)
            (P.filter fun q => q < p) (residueBad a)).card : ℤ) := by
  classical
  simpa only [residue_childCell_eq] using
    card_survivors_eq_sub_sum (residueCandidates Y H small a) P (residueBad a)

end NumberTheoryLean.SievePartition

end

section

namespace ErdosInverseCounts
open NumberTheoryLean NumberTheoryLean.SievePartition

theorem modulusCount_eq_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) (P : Finset ℕ) :
    modulusCount Y small a m = ResidueSieveTree.mass Y small a (m.primeFactors,P) := rfl

theorem primeFactors_product (H : Finset ℕ) (hH : ∀ p ∈ H,Nat.Prime p) :
    (∏ p ∈ H,p).primeFactors = H := by
  classical
  revert hH
  induction H using Finset.induction_on with
  | empty => intro _;simp
  | @insert p H hp ih =>
      intro hH
      have hprime := hH p (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ H,Nat.Prime q := fun q hq => hH q (Finset.mem_insert_of_mem hq)
      have hprod : (∏ q ∈ H,q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)
      rw [Finset.prod_insert hp,Nat.primeFactors_mul hprime.ne_zero hprod,hprime.primeFactors,
        ih hrest,Finset.singleton_union]

end ErdosInverseCounts

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualTagFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StoppedCountVertex

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePrefixRecurrence
open ReferenceForestTelescoping ReferencePruning SievePartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem included_subset (w : ℝ) (v : Vertex) : includedPrimes w v ⊆ v.available :=
  Finset.filter_subset _ _

theorem included_even (w : ℝ) (v : Vertex) (hi : v.node.side = .even) :
    includedPrimes w v = v.available := by simp [includedPrimes,hi,childAdmitted]

theorem child_rank_lt (w : ℝ) (v : Vertex) {p : ℕ} (hp : p ∈ v.available) :
    (child w v p).available.card < v.available.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨p,hp,lt_irrefl p⟩)

theorem countSurvivors_nonneg (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    0 ≤ countSurvivors Y small a v := Nat.cast_nonneg _

theorem count_partition (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    countSurvivors Y small a v = countMass Y small a v -
      ∑ p ∈ v.available,countSurvivors Y small a (child w v p) := by
  have h := residue_tree_identity Y v.required small v.available a
  unfold countSurvivors countMass child
  exact_mod_cast h

theorem reference_partition (w : ℝ) (v : Vertex) :
    referenceValue w v = v.scale - ∑ p ∈ includedPrimes w v,referenceValue w (child w v p) := by
  rw [referenceValue,reference_polynomial_recurrence,mul_sub,mul_one,Finset.mul_sum,
    includedPrimes,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : childAdmitted v.node.side v.node.gap (primeExponent w p)
  · simp only [ite_eq_left hp,referenceValue,child,step]
    ring
  · simp only [ite_eq_right hp,mul_zero]

theorem count_leaf (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex)
    (hv : v.available = ∅) : countSurvivors Y small a v = countMass Y small a v := by
  simpa only [hv,Finset.sum_empty,sub_zero] using count_partition w Y small a v

theorem reference_leaf (w : ℝ) (v : Vertex) (hv : v.available = ∅) : referenceValue w v = v.scale := by
  simpa only [includedPrimes,hv,Finset.filter_empty,Finset.sum_empty,sub_zero] using reference_partition w v

end NumberTheoryLean.StoppedCountVertex



namespace NumberTheoryLean.StoppedEvaluation

open _root_.Finset
open FinitePathGeometry StoppedCountVertex
attribute [local instance] Classical.propDecidable

theorem evaluate_sub (w : ℝ) (stop : List ℕ → Prop) (M₁ M₂ E₁ E₂ : Vertex → ℝ)
    (n : ℕ) (v : Vertex) :
    evaluate w stop (fun v => M₁ v-M₂ v) (fun v => E₁ v-E₂ v) n v =
      evaluate w stop M₁ E₁ n v-evaluate w stop M₂ E₂ n v := by
  induction n generalizing v with
  | zero => simp only [evaluate]; split_ifs <;> rfl
  | succ n ih =>
    simp only [evaluate]
    split_ifs
    · rfl
    · simp only [ih,Finset.sum_sub_distrib]
      ring

theorem evaluate_add (w : ℝ) (stop : List ℕ → Prop) (M₁ M₂ E₁ E₂ : Vertex → ℝ)
    (n : ℕ) (v : Vertex) :
    evaluate w stop (fun v => M₁ v+M₂ v) (fun v => E₁ v+E₂ v) n v =
      evaluate w stop M₁ E₁ n v+evaluate w stop M₂ E₂ n v := by
  induction n generalizing v with
  | zero => simp only [evaluate]; split_ifs <;> rfl
  | succ n ih =>
    simp only [evaluate]
    split_ifs
    · rfl
    · simp only [ih,Finset.sum_add_distrib]
      ring

theorem evaluate_reference (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) :
    evaluate w stop Vertex.scale (referenceValue w) n v = referenceValue w v := by
  induction n generalizing v with
  | zero =>
    have hv : v.available = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp only [evaluate]
    split_ifs
    · rfl
    · exact (reference_leaf w v hv).symm
  | succ n ih =>
    rw [evaluate]
    split_ifs
    · rfl
    · rw [reference_partition]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      apply ih
      have hlt := child_rank_lt w v (included_subset w v hp)
      omega

theorem stopped_count_reference_difference (w : ℝ) (Y : ℕ) (small : Finset ℕ)
    (a : ℕ → ℕ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (hn : v.available.card ≤ n) :
    stoppedCount w Y small a stop n v-referenceValue w v =
      evaluate w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0) n v +
      evaluate w stop (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z) n v := by
  rw [← evaluate_reference w stop n v hn]
  change evaluate w stop (countMass Y small a) (countSurvivors Y small a) n v - _ = _
  rw [← evaluate_sub]
  have h := evaluate_add w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0)
    (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z) n v
  simpa only [add_zero,zero_add] using h

end NumberTheoryLean.StoppedEvaluation



namespace NumberTheoryLean.StoppedVertexHistory

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex ReferenceForestTelescoping ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass

theorem after_required (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).required = v.required ∪ ps.toFinset := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change (after w (child w v p) ps).required = _
    rw [ih]
    ext q
    simp only [child,List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
    tauto

theorem after_available (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).available = suffixPrimes v.available ps := by
  induction ps generalizing v with
  | nil => simp [after,suffixPrimes_nil]
  | cons p ps ih =>
    change (after w (child w v p) ps).available = _
    rw [ih,suffixPrimes_cons]
    rfl

theorem after_scale (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale*prefixWeight ps := by
  induction ps generalizing v with
  | nil => simp [after,prefixWeight]
  | cons p ps ih =>
    change (after w (child w v p) ps).scale = _
    rw [ih]
    change (v.scale/(p:ℝ))*prefixWeight ps = v.scale*((p:ℝ)⁻¹*prefixWeight ps)
    ring

theorem prefixWeight_product (ps : List ℕ) : prefixWeight ps = ((ps.prod:ℕ):ℝ)⁻¹ := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    change (p:ℝ)⁻¹*prefixWeight ps = ((p*ps.prod:ℕ):ℝ)⁻¹
    rw [ih,Nat.cast_mul,mul_inv_rev]
    ring

theorem after_scale_product (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).scale = v.scale/((ps.prod:ℕ):ℝ) := by
  rw [after_scale,prefixWeight_product,div_eq_mul_inv]

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.StoppedCountLowerBound

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedEvaluation
attribute [local instance] Classical.propDecidable

theorem actual_stopped_bounds (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (hn : v.available.card ≤ n) :
    (v.node.side = .even → stoppedCount w Y small a stop n v ≤ countSurvivors Y small a v) ∧
    (v.node.side = .odd → countSurvivors Y small a v ≤ stoppedCount w Y small a stop n v) := by
  induction n generalizing v with
  | zero =>
    have hv : v.available = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    have he : stoppedCount w Y small a stop 0 v = countSurvivors Y small a v := by
      rw [stoppedCount,evaluate]
      split_ifs
      · rfl
      · exact (count_leaf w Y small a v hv).symm
    rw [he]
    exact ⟨fun _ => le_rfl,fun _ => le_rfl⟩
  | succ n ih =>
    have hRank : ∀ p ∈ v.available,(child w v p).available.card ≤ n := by
      intro p hp
      have hlt := child_rank_lt w v hp
      omega
    have hPart := count_partition w Y small a v
    constructor
    · intro hi
      unfold stoppedCount
      rw [evaluate]
      split_ifs
      · exact le_rfl
      · rw [included_even w v hi]
        have hsum : (∑ p ∈ v.available,countSurvivors Y small a (child w v p)) ≤
            ∑ p ∈ v.available,evaluate w stop (countMass Y small a) (countSurvivors Y small a) n (child w v p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact (ih (child w v p) (hRank p hp)).2 (by simp [child,step,hi,Side.flip])
        linarith
    · intro hi
      have hstop : ¬lowerStop stop v := by simp [lowerStop,hi]
      unfold stoppedCount
      rw [evaluate,ite_eq_right hstop]
      have hsum : (∑ p ∈ includedPrimes w v,
          evaluate w stop (countMass Y small a) (countSurvivors Y small a) n (child w v p)) ≤
          ∑ p ∈ includedPrimes w v,countSurvivors Y small a (child w v p) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (ih (child w v p) (hRank p (included_subset w v hp))).1 (by simp [child,step,hi,Side.flip])
      have hsub : (∑ p ∈ includedPrimes w v,countSurvivors Y small a (child w v p)) ≤
          ∑ p ∈ v.available,countSurvivors Y small a (child w v p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (included_subset w v)
          (fun p _ _ => countSurvivors_nonneg Y small a (child w v p))
      linarith

end NumberTheoryLean.StoppedCountLowerBound



namespace NumberTheoryLean.StoppedTraceSets

open _root_.Set _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory
attribute [local instance] Classical.propDecidable

theorem nil_not_childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) :
    [] ∉ childrenTraces P T := by simp [childrenTraces]

theorem sum_childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) (F : List ℕ → ℝ) :
    (∑ ps ∈ childrenTraces P T,F ps) = ∑ p ∈ P,∑ ps ∈ T p,F (p::ps) := by
  have hd : (P:Set ℕ).PairwiseDisjoint (fun p => (T p).image (List.cons p)) := by
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro ps hp hq
    obtain ⟨xp,_hxp,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨xq,_hxq,hxq⟩ := Finset.mem_image.mp hq
    exact hpq (List.cons.inj (hxp.trans hxq.symm)).1
  rw [childrenTraces,Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_image]
  intro a _ b _ heq
  exact (List.cons.inj heq).2

theorem stopped_lower (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : (after w v ps).node.side = .even := by
  induction n generalizing v ps with
  | zero =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact hs.1
    · exact False.elim (Finset.notMem_empty _ hp)
  | succ n ih =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact hs.1
    · obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      exact ih (child w v p) ht

theorem signed_childrenTraces (w : ℝ) (v : Vertex) (P : Finset ℕ)
    (T : ℕ → Finset (List ℕ)) (G : Vertex → ℝ) :
    (∑ ps ∈ childrenTraces P T,(-1:ℝ)^ps.length*G (after w v ps)) =
      -(∑ p ∈ P,∑ ps ∈ T p,(-1:ℝ)^ps.length*G (after w (child w v p) ps)) := by
  rw [sum_childrenTraces,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ps _
  simp only [List.length_cons,pow_succ,after]
  ring

end NumberTheoryLean.StoppedTraceSets



namespace NumberTheoryLean.FlatStoppedIdentity

open _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem flat_evaluate (w : ℝ) (stop : List ℕ → Prop) (M E : Vertex → ℝ) (n : ℕ) (v : Vertex) :
    evaluate w stop M E n v =
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*M (after w v ps)) +
      (∑ ps ∈ stopped w stop n v,(-1:ℝ)^ps.length*E (after w v ps)) := by
  induction n generalizing v with
  | zero =>
    by_cases hs : lowerStop stop v <;> simp [evaluate,expanded,stopped,traces,hs,after]
  | succ n ih =>
    by_cases hs : lowerStop stop v
    · simp [evaluate,expanded,stopped,traces,hs,after]
    · simp only [evaluate,hs,ite_false, if_false,expanded,stopped,traces]
      rw [Finset.sum_insert (nil_not_childrenTraces _ _),signed_childrenTraces,signed_childrenTraces]
      simp only [List.length_nil,pow_zero,after,one_mul]
      have hsum : (∑ p ∈ includedPrimes w v,evaluate w stop M E n (child w v p)) =
          ∑ p ∈ includedPrimes w v,
            ((∑ ps ∈ expanded w stop n (child w v p),(-1:ℝ)^ps.length*M (after w (child w v p) ps)) +
            (∑ ps ∈ stopped w stop n (child w v p),(-1:ℝ)^ps.length*E (after w (child w v p) ps))) :=
        Finset.sum_congr rfl (fun p _ => ih (child w v p))
      rw [hsum,Finset.sum_add_distrib]
      simp only [expanded,stopped]
      ring

theorem sideSign_after (w : ℝ) (v : Vertex) (ps : List ℕ) :
    sideSign (after w v ps).node.side = sideSign v.node.side*(-1:ℝ)^ps.length := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change sideSign (after w (child w v p) ps).node.side = _
    rw [ih]
    simp only [child,PrimeHistories.step,List.length_cons,pow_succ]
    cases v.node.side <;> simp only [Side.flip,sideSign] <;> ring

theorem stopped_sign_one (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hi : v.node.side = .even) {ps : List ℕ} (hp : ps ∈ stopped w stop n v) :
    (-1:ℝ)^ps.length = 1 := by
  have h := sideSign_after w v ps
  rw [stopped_lower w stop n v hp,hi] at h
  simpa only [sideSign,one_mul] using h.symm

theorem literal_stopped_difference (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) (hi : v.node.side = .even) :
    stoppedCount w Y small a stop n v-referenceValue w v =
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*
        (countMass Y small a (after w v ps)-(after w v ps).scale)) +
      (∑ ps ∈ stopped w stop n v,
        (countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) := by
  rw [stopped_count_reference_difference w Y small a stop n v hn,
    flat_evaluate w stop (fun z => countMass Y small a z-z.scale) (fun _ => 0),
    flat_evaluate w stop (fun _ => 0) (fun z => countSurvivors Y small a z-referenceValue w z)]
  simp only [mul_zero,Finset.sum_const_zero,add_zero,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro ps hp
  rw [stopped_sign_one w stop n v hi hp,one_mul]

theorem actual_reference_error_lower_bound (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hn : v.available.card ≤ n) (hi : v.node.side = .even) :
    referenceValue w v +
      (∑ ps ∈ expanded w stop n v,(-1:ℝ)^ps.length*
        (countMass Y small a (after w v ps)-(after w v ps).scale)) +
      (∑ ps ∈ stopped w stop n v,
        (countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) ≤
      countSurvivors Y small a v := by
  have h := literal_stopped_difference w Y small a stop n v hn hi
  have hL := (StoppedCountLowerBound.actual_stopped_bounds w Y small a stop n v hn).1 hi
  linarith

end NumberTheoryLean.FlatStoppedIdentity



namespace NumberTheoryLean.StoppedTraceAdmission

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedTraceSets
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_nil_mem (w : ℝ) (v : Vertex) :
    [] ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  apply Finset.mem_filter.mpr
  exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,trivial⟩

theorem reference_child_cons (w : ℝ) (v : Vertex) {p : ℕ} (hp : p ∈ includedPrimes w v)
    {ps : List ℕ} (hps : ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  have hchild := Finset.mem_filter.mp hp
  have htail := Finset.mem_filter.mp hps
  have hSuf : ps ∈ decreasingPrefixes (suffixPrimes v.available [p]) := by
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail.1
  have hdec := (append_mem_decreasing_iff (singleton_prefix_mem hchild.1)).mpr hSuf
  apply Finset.mem_filter.mpr
  refine ⟨by simpa only [List.singleton_append] using hdec,?_⟩
  exact ⟨hchild.2,htail.2⟩

theorem trace_reference_member (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) :
    ps ∈ referencePrefixes w v.available v.node.side v.node.gap := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
  | succ n ih =>
    by_cases hs : StoppedEvaluation.lowerStop stop v
    · have heq : ps = [] := by simpa [expanded,stopped,traces,hs] using hp
      subst ps
      exact reference_nil_mem w v
    · rcases hp with hExp | hStop
      · simp only [expanded,traces,hs,ite_false, if_false,Finset.mem_insert] at hExp
        rcases hExp with rfl | hExp
        · exact reference_nil_mem w v
        · obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hExp
          obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
          exact reference_child_cons w v hp (ih (child w v p) (Or.inl ht))
      · simp only [stopped,traces,hs,ite_false, if_false] at hStop
        obtain ⟨p,hp,hps⟩ := Finset.mem_biUnion.mp hStop
        obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
        exact reference_child_cons w v hp (ih (child w v p) (Or.inr ht))

theorem trace_nodup (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ps.Nodup := by
  have h := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp (trace_reference_member w stop n v hp)).1).1
  exact h.imp (fun h => ne_of_gt h)

theorem trace_primes (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hP : ∀ p ∈ v.available,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ∀ p ∈ ps,Nat.Prime p := by
  have h := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp (trace_reference_member w stop n v hp)).1).2
  intro p hps
  exact hP p (h p hps)

end NumberTheoryLean.StoppedTraceAdmission



namespace NumberTheoryLean.StoppedCountAdapters

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedEvaluation StoppedVertexHistory
open StoppedTraceSets FlatStoppedIdentity ReferenceAdmission ReferencePruning
attribute [local instance] Classical.propDecidable

theorem countMass_eq_tree_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    countMass Y small a v = (ResidueSieveTree.mass Y small a (v.required,v.available) : ℝ) := by
  simp only [countMass,ResidueSieveTree.mass,Int.cast_natCast]

theorem root_after_mass (w : ℝ) (Y : ℕ) (small H P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (ps : List ℕ) :
    countMass Y small a (after w (rootVertex z H P mu) ps) =
      (ResidueSieveTree.mass Y small a (H ∪ ps.toFinset,suffixPrimes P ps) : ℝ) := by
  rw [countMass_eq_tree_mass,after_required,after_available]
  rfl

end NumberTheoryLean.StoppedCountAdapters



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.LogarithmicBinPartition

open _root_.Set _root_.Finset
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels ErdosInversePrimeBin

theorem mem_sourcePrimeSet {w z : ℝ} (hw : 0 < w) (hwz : w < z) (p : ℕ) :
    p ∈ sourcePrimeSet w z ↔ p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  constructor
  · intro hp
    obtain ⟨hup,hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hup
    refine ⟨hprime,?_,(Nat.le_floor_iff (hw.trans hwz).le).mp hbound⟩
    by_contra! hlo
    exact hnot (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hw.le).mpr hlo,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (hw.trans hwz).le).mpr hhi,hprime⟩,?_⟩
    intro hp
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hw.le).mp (Nat.mem_primesLE.mp hp).1)

end NumberTheoryLean.LogarithmicBinPartition



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

theorem typedState_ratio (i : Side) (s : ℝ) (hs : Valid i s) : stateRatio (typedState i s hs) = s := by
  cases i <;> rfl

variable {w ell S : ℝ} {start : Node}

theorem source_gap (hr : 0 < start.gap) (hs : Valid start.side start.ratio) :
    gapValue (Real.log start.gap) (sourceCostState hs) = start.gap := by
  simp [gapValue,sourceCostState,Real.exp_log hr]

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound PrimeKilledChain

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_NonnegativeOriginalOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCompactOccupation

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights PrimeCorrectionFactor
open FlaggedOccupationBound PersistentFailureFlag ActualProcessCoupling ActualFlaggedCompact

variable {w ell S B : ℝ} {start : Node}

theorem literal_scaled_weight (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    B^2*ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal*scaledWeight w B start (some h) := by
  rw [PrimeChainProbabilities.source_prime_weight_identity hell hr hs h]
  unfold scaledWeight
  ring

end NumberTheoryLean.SourceCompactOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open PrimeCompactWeights SourceCompactOccupation
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem singleton_off_stage (n : ℕ) (h : History w ell S start) (hne : h.primes.length ≠ n) :
    pathLaw w ell S start n {some h} = 0 := by
  have hsub : ({some h} : Set (ChainState w ell S start)) ⊆ {z | ¬stage n z} := by
    intro z hz
    have he : z = some h := hz
    subst z
    exact hne
  exact measure_mono_null hsub (ae_iff.mp (pathLaw_stage n))

theorem singleton_scaled_reward (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (n : ℕ) (h : History w ell S start)
    (F : List ℕ → ℝ) :
    (pathLaw w ell S start n).real {some h} *
      (scaledWeight w B start (some h)*F h.primes) =
      if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
  classical
  by_cases hn : n = h.primes.length
  · rw [ite_eq_left hn,hn,measureReal_def]
    rw [← mul_assoc,← literal_scaled_weight hell hr hs h]
  · rw [ite_eq_right hn,measureReal_def,singleton_off_stage n h (Ne.symm hn)]
    simp

theorem finite_signed_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
        ∑ h : History w ell S start,
          if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
    let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
    rw [integral_fintype Integrable.of_finite,Fintype.sum_option]
    simp only [scaledWeight,listReward,mul_zero,smul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro h _hh
    exact singleton_scaled_reward (by linarith) hr hs n h F
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hlen (h : History w ell S start) : h.primes.length ∈ range (LowStateHorizon.sourceHorizon S B) :=
    mem_range.mpr (PrimeHistoryHorizon.history_length_lt hell hS0 hr hs hB hsize h)
  simp only [Finset.sum_ite_eq',hlen,ite_true, if_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using sum_histories hw1 start (fun ps => prefixWeight ps*F ps)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactWeights
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem listReward_nonneg (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) (z : ChainState w ell S start) :
    0 ≤ listReward F z := by
  cases z with
  | none => exact le_rfl
  | some h => exact hF h.primes h.admissible

theorem finite_nonnegative_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫⁻ z,ENNReal.ofReal (scaledWeight w B start z*listReward F z) ∂pathLaw w ell S start n) =
      ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hnon (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z*listReward F z :=
    mul_nonneg (scaledWeight_nonneg hs z) (listReward_nonneg F hF z)
  rw [← finite_signed_original_occupation hw hell hS0 hS hr hs hsS hB hsize F]
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => integral_nonneg hnon)]
  apply Finset.sum_congr rfl
  intro n _hn
  let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall hnon)).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSuccessfulTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels PrimeHistories PrimeKilledChain
open SuccessfulTailTransport ExponentialMesh UniformBudgetRate LowStateHorizon
open RegeneratingInverseBands CostPrefixTransport

theorem even_source_cost_state {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) :
    ∃ s : EvenState,s.1 = start.ratio ∧ FlaggedSourceStart.sourceCostState hs = (.inl s,0) := by
  cases start with
  | mk i s r cap closed =>
    change i = .even at hi
    subst i
    exact ⟨⟨s,hs⟩,rfl,rfl⟩

end NumberTheoryLean.SourceSuccessfulTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectedCompactTransfer
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousCompactHighError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CompactTestGeometry CompactInverseTest
open RegeneratingInverseBands InvariantInverseWeights OriginalHarmonicOccupation
open ContinuousHighPartition FlaggedHarmonicTransform
open LowStateHorizon AdmittedHarmonicPaths

theorem phase_compact_bound {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (hH .even).bounded_above_of_compact_support (hcompact .even)
  obtain ⟨Ao,ho⟩ := (hH .odd).bounded_above_of_compact_support (hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

end NumberTheoryLean.ContinuousCompactHighError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceLowRemoval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceLowRemoval

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures TransitionKernels FinitePathGeometry DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousCompactHighError OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon

theorem scaleConstant_pos : 0 < scaleConstant := by
  unfold scaleConstant
  exact div_pos (by norm_num) (phiEven_pos (by norm_num))

theorem source_scale_upper {v B : ℝ} (hB : 0 < B) (s : EvenState) (hs : s.1 ≤ 23/10)
    (hcut : currentExponent v (.inl s,0) = B) :
    (Real.exp v)^2/stateWeight (.inl s) ≤ scaleConstant*B^2 ∧ gapValue v (.inl s,0) ≤ (23/10:ℝ)*B := by
  have hs0 : 0 < s.1 := by linarith [s.2]
  have he : Real.exp v = B*s.1 := by
    change Real.exp (v-0)/s.1 = B at hcut
    rw [sub_zero] at hcut
    exact (div_eq_iff hs0.ne').mp hcut
  have hupper : Real.exp v ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hsq : (Real.exp v)^2 ≤ (23/10:ℝ)^2*B^2 := by nlinarith [Real.exp_pos v]
  have hφ : 0 < phiEven s.1 := phiEven_pos (by linarith [s.2])
  have hφend : 0 < phiEven (23/10) := phiEven_pos (by norm_num)
  have hmono : phiEven (23/10) ≤ phiEven s.1 :=
    TwoStepDensityBounds.weight_antitone (i:=.even) s.2 (by norm_num [Valid]) hs
  have hinv := one_div_le_one_div_of_le hφend hmono
  refine ⟨?_,?_⟩
  · change (Real.exp v)^2/phiEven s.1 ≤ _
    calc
      _ = (Real.exp v)^2*(1/phiEven s.1) := by ring
      _ ≤ ((23/10:ℝ)^2*B^2)*(1/phiEven (23/10)) := mul_le_mul hsq hinv (by positivity) (by positivity)
      _ = _ := by unfold scaleConstant; ring
  · simpa only [gapValue,sub_zero] using hupper

end NumberTheoryLean.SourceLowRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceNodeCoordinates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceNodeCoordinates

open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RegeneratingInverseBands ArrivalKernelGeometry SourceLowRemoval SourceSuccessfulTail
open InvariantInverseWeights DerivativeWeights

theorem node_gap_eq {B : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : start.cutoff=B) : start.gap=B*start.ratio := by
  have he : start.cutoff=start.gap/start.ratio := hcons
  rw [hcut] at he
  exact ((eq_div_iff (valid_pos hs).ne').mp he).symm

theorem source_node_bounds {B : ℝ} (hB : 0 < B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    Valid start.side start.ratio ∧ 0 < start.gap ∧ B ≤ start.gap ∧ start.gap ≤ (23/10:ℝ)*B := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he := node_gap_eq hs hcons hcut
  refine ⟨hs,?_,?_,?_⟩
  · rw [he]; exact mul_pos hB (valid_pos hs)
  · nlinarith
  · nlinarith

theorem source_currentExponent {start : Node} (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hcons : Consistent start) :
    currentExponent (Real.log start.gap) (FlaggedSourceStart.sourceCostState hs)=start.cutoff := by
  unfold currentExponent
  rw [FlaggedSourceStart.source_gap hr hs]
  change start.gap/stateRatio (FlaggedSourceStart.typedState start.side start.ratio hs)=start.cutoff
  rw [FlaggedSourceStart.typedState_ratio]
  exact hcons.symm

theorem node_scale_upper {B : ℝ} (hB : 0 < B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    start.gap^2/weight start.side start.ratio ≤ scaleConstant*B^2 := by
  obtain ⟨hs,hr,_,_⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have hcurrent := source_currentExponent hr hs hcons
  rw [hcost,hcut] at hcurrent
  have h := (source_scale_upper hB s (by simpa only [hsv] using h23) hcurrent).1
  have hweight : stateWeight (.inl s)=weight start.side start.ratio := by
    rw [hi]
    change phiEven s.1=phiEven start.ratio
    rw [hsv]
  rw [Real.exp_log hr,hweight] at h
  exact h

end NumberTheoryLean.SourceNodeCoordinates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UncappedHighRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualPrimeHigh
open _root_.Filter
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership

theorem uncapped_rewarded_high_removal : ∃ M w₀ : ℝ, 0 < M ∧ 1 < w₀ ∧
    ∀ c : ℝ, 0 < c → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ z : Node,
        z.cutoff = B → 0 < z.gap → Valid z.side z.ratio → Consistent z →
        uncappedRewardedHighMass w ell z ((Real.log B)^2) c ≤ M*B^(-A) := by
  obtain ⟨M,w₀,hM,hw₀,hbound⟩ := ErdosPrimeInputs.HighPrimeRemoval.rewarded_high_removal
  refine ⟨M,w₀,hM,hw₀,?_⟩
  intro c hc A
  filter_upwards [hbound c hc A] with B hB
  intro w hw ell hell hellB z hcut hr hs hz
  have h := uncapped_rewarded_mass_le (hw₀.trans_le hw) (by linarith : 0 ≤ ell) hr hs hz
    ((Real.log B)^2) c
  rw [hcut] at h
  exact h.trans (hB w hw ell hell hellB z.gap)

end NumberTheoryLean.ActualPrimeHigh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompactSelectedPartition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ActualPrimeHigh

theorem retained_no_high {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hsS : start.ratio ≤ S) (hp : allowed w ell S start ps) :
    ¬actualHasHigh w S start ps := by
  rintro ⟨pre,suf,he,hh⟩
  have hpre := (allowed_append w ell S start pre suf).mp (he ▸ hp) |>.1
  exact (not_lt_of_ge (terminal_ratio_le hsS hpre)) hh

theorem allowed_of_uncapped_prefix_ceiling {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps)
    (hbound : ∀ pre suf : List ℕ, ps = pre++suf → (terminal w start pre).ratio ≤ S) :
    allowed w ell S start ps := by
  classical
  induction ps generalizing start with
  | nil => exact allowed_nil w ell S start
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hpS : (step w start p).ratio ≤ S := by
      simpa only [terminal_cons,terminal_nil] using hbound [p] ps rfl
    have hb : ∀ pre suf : List ℕ, ps = pre++suf →
        (terminal w (step w start p) pre).ratio ≤ S := by
      intro pre suf he
      exact hbound (p::pre) suf (by rw [List.cons_append,he])
    obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell S start p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hpS⟩,ih ht hb⟩

theorem allowed_iff_uncapped_no_high {w ell S : ℝ} {start : Node} (hsS : start.ratio ≤ S)
    (ps : List ℕ) : allowed w ell S start ps ↔
      uncappedAllowed w ell start ps ∧ ¬actualHasHigh w S start ps := by
  constructor
  · intro hp
    exact ⟨(uncapped_iff_exists_ceiling w ell start ps).mpr ⟨S,hsS,hp⟩,retained_no_high hsS hp⟩
  · rintro ⟨hp,hh⟩
    apply allowed_of_uncapped_prefix_ceiling hp
    intro pre suf he
    exact le_of_not_gt (fun h => hh ⟨pre,suf,he,h⟩)

theorem retained_eq_nonhigh {w ell S : ℝ} (hw : 1 < w) {start : Node} (hsS : start.ratio ≤ S) :
    retainedPrefixes w ell S start =
      (uncappedPrefixes w ell start).filter (fun ps => ¬actualHasHigh w S start ps) := by
  classical
  ext ps
  rw [mem_retainedPrefixes hw,Finset.mem_filter,mem_uncappedPrefixes hw]
  exact allowed_iff_uncapped_no_high hsS ps

theorem uncapped_sum_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (F : List ℕ → ℝ) :
    (∑ ps ∈ uncappedPrefixes w ell start,F ps) =
      (∑ ps ∈ retainedPrefixes w ell S start,F ps) +
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),F ps := by
  classical
  rw [retained_eq_nonhigh hw hsS]
  exact (Finset.sum_filter_not_add_sum_filter _ _ _).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_LiteralUniformPrimeTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem removed_signed_reward_bound {w ell S c : ℝ} (hw : 1 < w)
    {start : Node} (hsS : start.ratio ≤ S) (F : List ℕ → ℝ)
    (hF : ∀ ps ∈ uncappedPrefixes w ell start,
      |F ps| ≤ Real.exp (-c*(terminal w start ps).gap)) :
    |(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
      (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)| ≤
      uncappedRewardedHighMass w ell start S c := by
  classical
  have hp := uncapped_sum_partition (ell := ell) hw hsS (fun ps => prefixWeight ps*F ps)
  have he : (∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
      (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) =
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),prefixWeight ps*F ps := by
    linarith only [hp]
  rw [he]
  calc
    _ ≤ ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),
        |prefixWeight ps*F ps| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ps hps
      rw [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
      exact mul_le_mul_of_nonneg_left (hF ps (Finset.mem_filter.mp hps).1) (prefixWeight_nonneg ps)

theorem removed_signed_reward_every_power :
    ∃ M w₀ : ℝ,0 < M ∧ 1 < w₀ ∧ ∀ c : ℝ,0 < c → ∀ A : ℝ,∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ,w₀ ≤ w → ∀ ell : ℝ,1 ≤ ell → ell ≤ B → ∀ start : Node,
        start.cutoff = B → 0 < start.gap → Valid start.side start.ratio → Consistent start →
        start.ratio ≤ (Real.log B)^2 → ∀ F : List ℕ → ℝ,
        (∀ ps ∈ uncappedPrefixes w ell start,|F ps| ≤ Real.exp (-c*(terminal w start ps).gap)) →
        |(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
          (∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*F ps)| ≤ M*B^(-A) := by
  obtain ⟨M,w₀,hM,hw₀,hbound⟩ := uncapped_rewarded_high_removal
  refine ⟨M,w₀,hM,hw₀,?_⟩
  intro c hc A
  filter_upwards [hbound c hc A] with B hB
  intro w hw ell hell hellB start hcut hr hs hcons hsS F hF
  exact (removed_signed_reward_bound (hw₀.trans_le hw) hsS F hF).trans
    (hB w hw ell hell hellB start hcut hr hs hcons)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.LiteralPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeFamilyOccupation
open PrimeCompactWeights CompactInverseTest CompactNormalizationCorrection ScaledOriginalTail DerivativeWeights
open ErdosPrimeInputs.PrimePrefixMass

theorem tailListReward_nonneg (c K w : ℝ) (start : Node) (ps : List ℕ) : 0 ≤ tailListReward c K w start ps := by
  unfold tailListReward
  split_ifs <;> positivity

theorem tail_weight_test_identity {w ell S B : ℝ} {start : Node} (c K : ℝ) (z : ChainState w ell S start) :
    ENNReal.ofReal (scaledWeight w B start z*listReward (tailListReward c K w start) z) = scaledTail c K w B start z := by
  cases z with
  | none => simp [scaledWeight,listReward,scaledTail]
  | some h =>
    change ENNReal.ofReal (scaledWeight w B start (some h)*(if K < h.node.gap then Real.exp (-c*h.node.gap) else 0)) = _
    change ENNReal.ofReal (scaledWeight w B start (some h)*(if K < h.node.gap then Real.exp (-c*h.node.gap) else 0)) =
      if K < h.node.gap then ENNReal.ofReal (scaledWeight w B start (some h)*Real.exp (-c*h.node.gap)) else 0
    by_cases hh : K < h.node.gap
    · rw [ite_eq_left hh,ite_eq_left hh]
    · rw [ite_eq_right hh,ite_eq_right hh,mul_zero,ENNReal.ofReal_zero]

theorem literal_scaled_tail {w ell S B : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B) (c K : ℝ) :
    ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*tailListReward c K w start ps)) =
      ∑ n ∈ range (LowStateHorizon.sourceHorizon S B),∫⁻ z,scaledTail c K w B start z ∂pathLaw w ell S start n := by
  have he := finite_nonnegative_original_occupation hw hell hS0 hS hr hs hsS hB hsize
    (tailListReward c K w start) (fun ps _ => tailListReward_nonneg c K w start ps)
  simp_rw [tail_weight_test_identity c K] at he
  exact he.symm

end NumberTheoryLean.LiteralPrimeOccupation

end

section

namespace NumberTheoryLean.LiteralUniformPrimeTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualPrimeHigh PrimeFamilyOccupation LiteralPrimeOccupation ScaledOriginalTail
open UniformBudgetRate LowStateHorizon ErdosPrimeInputs.PrimePrefixMass

theorem tailListReward_envelope (c K w : ℝ) (start : Node) (ps : List ℕ) :
    |tailListReward c K w start ps| ≤ Real.exp (-c*(terminal w start ps).gap) := by
  unfold tailListReward
  split_ifs
  · rw [abs_of_pos (Real.exp_pos _)]
  · rw [abs_zero]; exact (Real.exp_pos _).le

theorem actual_uniform_original_prime_tail (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        B^2*(∑ ps ∈ uncappedPrefixes w ell start,
          prefixWeight ps*tailListReward c (3*((M:ℝ)+1)) w start ps) ≤ ε := by
  obtain ⟨M₀,BL,wL,hBL,hwL,hlow⟩ := actual_uniform_scaled_tail_jb247 d c (ε/2) hd hc (by linarith)
  obtain ⟨Crem,wH,hCrem,hwH,hremove⟩ := removed_signed_reward_every_power
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp (hremove c hc 3)
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  let B₀ := max BL (max BH (max (Real.exp 2) (2*Crem/ε)))
  let w₀ := max wL (max wH (max normalizationThreshold wScale))
  refine ⟨M₀,B₀,w₀,hBL.trans_le (le_max_left _ _),hwL.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hBexp : Real.exp 2 ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBlarge : 2*Crem/ε ≤ B :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hwL' : wL ≤ w := (le_max_left _ _).trans hw
  have hwH' : wH ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hwScale' : wScale ≤ w :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound (hwScale w hwScale') hlogB hcomp
  let S := (Real.log B)^2
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hsS : start.ratio ≤ S := by linarith
  have he : B*start.ratio = start.gap := by
    have hh : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at hh
    exact (eq_div_iff (valid_pos hs).ne').mp hh
  have hr : 0 < start.gap := by rw [← he]; exact mul_pos hBpos (valid_pos hs)
  have hsize : start.gap ≤ (23/10:ℝ)*B := by nlinarith
  let F := tailListReward c (3*((M:ℝ)+1)) w start
  have hretained : B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) ≤ ε/2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ ε/2)).mp
    rw [literal_scaled_tail hnorm hell hS0 hscale.1 hr hs hsS hBpos hsize]
    exact hlow M hM B w hBL' hwL' ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hremoved := hBH B hBH' w hwH' ell hell hellB start hcut hr hs hcons hsS F
    (fun ps _ => tailListReward_envelope c (3*((M:ℝ)+1)) w start ps)
  have hremovedScaled : B^2*(Crem*B^(-(3:ℝ))) ≤ ε/2 := by
    have heq : B^2*(Crem*B^(-(3:ℝ))) = Crem/B := by
      rw [Real.rpow_neg hBpos.le,Real.rpow_ofNat]
      field_simp
    rw [heq]
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBlarge
    nlinarith
  have hdiff := mul_le_mul_of_nonneg_left hremoved (sq_nonneg B)
  have htriangle : B^2*(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) ≤
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)+
        B^2*|(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps)-
          (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self
      ((∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps)-
       (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps))) (sq_nonneg B)
    nlinarith
  linarith

end NumberTheoryLean.LiteralUniformPrimeTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_LiteralCompactRemoval
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.LiteralCompactRemoval

open _root_.Set _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualPrimeHigh PrimeFamilyOccupation LiteralPrimeOccupation SourceNodeCoordinates
open ContinuousCompactHighError SourceLowRemoval DerivativeWeights
open ErdosPrimeInputs.PrimePrefixMass

theorem compact_exponential_envelope {H : Side → ℝ×ℝ → ℝ} {A K : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ i x,|H i x| ≤ A)
    (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0)
    (w : ℝ) (start : Node) (ps : List ℕ) :
    |nodeReward H w start ps| ≤ ((A+1)*Real.exp K)*Real.exp (-(terminal w start ps).gap) := by
  by_cases hr : (terminal w start ps).gap ≤ K
  · have he : 1 ≤ Real.exp (K-(terminal w start ps).gap) := Real.one_le_exp_iff.mpr (by linarith)
    have hb := hbound (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio)
    change |H _ _| ≤ _
    rw [mul_assoc,← Real.exp_add]
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ A+1 by linarith)
    simp only [sub_eq_add_neg] at hh
    linarith
  · have hz := hsupport (terminal w start ps).side (terminal w start ps).gap (terminal w start ps).ratio (lt_of_not_ge hr)
    simp only [nodeReward,hz,abs_zero]
    positivity

theorem weighted_sum_div (I : Finset (List ℕ)) (F : List ℕ → ℝ) (D : ℝ) :
    (∑ ps ∈ I,prefixWeight ps*(F ps/D)) = (∑ ps ∈ I,prefixWeight ps*F ps)/D := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ps _hp
  ring

theorem source_compact_family_removal {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∃ C w₀ : ℝ,0 ≤ C ∧ 1 < w₀ ∧ ∀ᶠ B : ℝ in atTop,∀ w : ℝ,w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |uncappedFamilyValue H w ell start-familyValue H w ell ((Real.log B)^2) start| ≤ C/B := by
  obtain ⟨A,hA,hbound⟩ := phase_compact_bound hH hcompact
  let D := (A+1)*Real.exp K
  have hD : 0 < D := by dsimp [D] <;> positivity
  obtain ⟨M,w₀,hM,hw₀,hremove⟩ := removed_signed_reward_every_power
  refine ⟨scaleConstant*M*D,w₀,by have hh := scaleConstant_pos; positivity,hw₀,?_⟩
  filter_upwards [hremove 1 (by norm_num) 3,eventually_ge_atTop (Real.exp 2)] with B hrem hBexp
  intro w hw ell hell hellB start hi h199 h23 hcons hcut
  have hB : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  obtain ⟨hs,hr,_,_⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  let F := nodeReward H w start
  have hF : ∀ ps ∈ uncappedPrefixes w ell start,|F ps/D| ≤ Real.exp (-(1:ℝ)*(terminal w start ps).gap) := by
    intro ps _hp
    rw [abs_div,abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    have h := compact_exponential_envelope hA hbound hsupport w start ps
    simpa only [neg_mul,one_mul,mul_comm] using h
  have herror := hrem w hw ell hell hellB start hcut hr hs hcons hsS (fun ps => F ps/D) hF
  rw [weighted_sum_div,weighted_sum_div,← sub_div,abs_div,abs_of_pos hD] at herror
  have hdiff := (div_le_iff₀ hD).mp herror
  have hscale := node_scale_upper hB start hi h199 h23 hcons hcut
  have hnormal : 0 ≤ start.gap^2/weight start.side start.ratio := div_nonneg (sq_nonneg _) (weight_pos hs).le
  change |(start.gap^2/weight start.side start.ratio)*(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps)-
    (start.gap^2/weight start.side start.ratio)*(∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*F ps)| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg hnormal]
  calc
    _ ≤ (scaleConstant*B^2)*((M*B^(-(3:ℝ)))*D) :=
      mul_le_mul hscale hdiff (abs_nonneg _) (mul_nonneg scaleConstant_pos.le (sq_nonneg _))
    _ = _ := by
      rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
      field_simp

end NumberTheoryLean.LiteralCompactRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeOccupationDensity
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OriginalPrimeOccupationLimit

open _root_.Set _root_.Filter
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership
open LiteralPrimeOccupation LiteralCompactRemoval RetainedOccupationLimit
open CompactLogOccupationTest NormalizedOccupationLimit

theorem original_prime_continuous_occupation_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |uncappedFamilyValue H w ell start-invariantAverage (arrivalTest ell H)| ≤ ε := by
  obtain ⟨BP,wP,hBP,hwP,hretained⟩ := retained_original_occupation_limit_jb247 hH hcompact ha hb hell hsupport d (ε/2) hd (by linarith)
  obtain ⟨C,wH,hC,hwH,hremove⟩ := source_compact_family_removal hH hcompact
    (K:=b) (fun i r s h => hsupport i r s (Or.inr h))
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp hremove
  let B₀ := max BP (max BH (max ell (2*C/ε)))
  refine ⟨B₀,max wP wH,hBP.trans_le (le_max_left _ _),hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBP' : BP ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hellB : ell ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hlarge : 2*C/ε ≤ B :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBP.trans_le hBP'
  have hsmall : C/B ≤ ε/2 := by
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have hrem := hBH B hBH' w ((le_max_right _ _).trans hw) ell hell hellB start hi h199 h23 hcons hcut
  have hret := hretained B w hBP' ((le_max_left _ _).trans hw) hcomp start hi h199 h23 hcons hcut
  have htri := abs_sub_le (uncappedFamilyValue H w ell start) (familyValue H w ell ((Real.log B)^2) start)
    (invariantAverage (arrivalTest ell H))
  linarith

end NumberTheoryLean.OriginalPrimeOccupationLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_UncappedCompactMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UncappedCompactMass

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeCompactWeights
open ActualPrimeHigh SourceNodeCoordinates LiteralCompactRemoval LiteralPrimeOccupation
open PositiveGapMajorant OriginalPrimeOccupationLimit CompactLogOccupationTest NormalizedOccupationLimit
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem uncapped_terminal_ratio_le_gap {w ell : ℝ} {start : Node} {ps : List ℕ}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (hp : uncappedAllowed w ell start ps) :
    0 < (terminal w start ps).ratio ∧ (terminal w start ps).ratio ≤ (terminal w start ps).gap := by
  obtain ⟨U,_hU,hpU⟩ := (uncapped_iff_exists_ceiling w ell start ps).mp hp
  exact ⟨valid_pos (terminal_valid hs hpU),history_ratio_le_gap hell hr hs hc hcut ⟨ps,hpU⟩⟩

theorem uniform_uncapped_compact_mass (K ell d : ℝ) (hK : 3 ≤ K) (hell : 1 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*compactPrefixMass K w ell start ≤ C := by
  obtain ⟨H,hcompact,hbounds,hOne,hzero⟩ := exists_positive_gap_majorant K
  let HH : Side → ℝ×ℝ → ℝ := fun _ => H
  have hH : ∀ i,Continuous (HH i) := fun _ => H.continuous
  have hCpt : ∀ i,HasCompactSupport (HH i) := fun _ => hcompact
  have hsupport : ∀ i : Side,∀ r s : ℝ,r<1 ∨ K+1 < r → HH i (r,s)=0 := fun _ => hzero
  obtain ⟨BL,w₀,hBL,hw₀,hlim⟩ := original_prime_continuous_occupation_limit hH hCpt
    (by norm_num : 0 < (1:ℝ)) (by linarith : 0 < K+1) hell hsupport d 1 hd (by norm_num)
  let L : ℝ := |invariantAverage (arrivalTest ell HH)|+1
  let W : ℝ := weight .even (199/100)
  have hL : 0 < L := by dsimp [L] <;> positivity
  have hW : 0 < W := weight_pos (by norm_num [Valid])
  refine ⟨W*L,max BL ell,w₀,mul_pos hW hL,hBL.trans_le (le_max_left _ _),hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hellB : ell ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  obtain ⟨hs,hr,hBgap,_hsize⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hlimit := hlim B w hBL' hw hcomp start hi h199 h23 hcons hcut
  have hnorm : uncappedFamilyValue HH w ell start ≤ L := by
    have hu := (abs_le.mp hlimit).2
    have hab := le_abs_self (invariantAverage (arrivalTest ell HH))
    dsimp only [L]
    linarith
  let Z : ℝ := ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*nodeReward HH w start ps
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun ps _ => mul_nonneg (prefixWeight_nonneg ps) (hbounds _).1)
  have hdom : compactPrefixMass K w ell start ≤ Z := by
    apply Finset.sum_le_sum
    intro ps hp
    apply mul_le_mul_of_nonneg_left _ (prefixWeight_nonneg ps)
    change (if 2 ≤ (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ K then 1 else 0) ≤
      H ((terminal w start ps).gap,(terminal w start ps).ratio)
    split_ifs with hgap
    · have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
      have hratio := uncapped_terminal_ratio_le_gap hell hr hs hcons (by rwa [hcut]) hpA
      rw [hOne _ _ hgap.1 hgap.2 hratio.1.le (hratio.2.trans hgap.2)]
    · exact (hbounds _).1
  have hwpos := weight_pos hs
  have hwupper : weight start.side start.ratio ≤ W := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (by rwa [hi] at hs) h199
  have hsq : B^2 ≤ start.gap^2 := by nlinarith
  calc
    B^2*compactPrefixMass K w ell start ≤ B^2*Z := mul_le_mul_of_nonneg_left hdom (sq_nonneg B)
    _ ≤ start.gap^2*Z := mul_le_mul_of_nonneg_right hsq hZ
    _ = weight start.side start.ratio*uncappedFamilyValue HH w ell start := by
      unfold uncappedFamilyValue
      dsimp only [Z]
      field_simp
    _ ≤ weight start.side start.ratio*L := mul_le_mul_of_nonneg_left hnorm hwpos.le
    _ ≤ W*L := mul_le_mul_of_nonneg_right hwupper hL.le

end NumberTheoryLean.UncappedCompactMass

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped BigOperators

theorem all_integer_euler_product (z : ℕ) (hz : 1 ≤ z) :
    (∏ n ∈ Finset.Icc 2 z, (1 - (n : ℝ)⁻¹)) = (z : ℝ)⁻¹ := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
      have hzs : ((z + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem smallEuler_ge_inv (z : ℕ) (hz : 2 ≤ z) : (z : ℝ)⁻¹ ≤ smallEuler z := by
  have hsubset : LargePrimeDeletion.cutoffPrimes z ⊆ Finset.Icc 2 z := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, hpz⟩
  rw [← all_integer_euler_product z (by omega)]
  apply Finset.prod_le_prod_of_subset_of_le_one hsubset
  · intro n hn
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega))
  · intro n _ _
    have h := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n)
    linarith

theorem smallEuler_floor_ge_inv (u : ℝ) (hu : 2 ≤ u) : u⁻¹ ≤ smallEuler ⌊u⌋₊ := by
  have hz : 2 ≤ ⌊u⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  have hzpos : (0 : ℝ) < (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊u⌋₊ by omega)
  exact ((inv_le_inv₀ (by linarith) hzpos).mpr (Nat.floor_le (by linarith))).trans (smallEuler_ge_inv _ hz)

end NumberTheoryLean.SmallSieveFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LastPrimeModulusCount
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StoppedModulusCount

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedTraceSets
open StoppedTraceAdmission StoppedCountAdapters ReferencePruning ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem trace_product_eq_finset (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) :
    (∏ p ∈ ps.toFinset,p) = ps.prod := by
  simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) (trace_nodup w stop n v hp)

theorem trace_primeFactors (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hP : ∀ p ∈ v.available,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ps.prod.primeFactors = ps.toFinset := by
  have hprime : ∀ p ∈ ps.toFinset,Nat.Prime p :=
    fun p hp' => trace_primes w stop n v hP hp p (List.mem_toFinset.mp hp')
  have h := ErdosInverseCounts.primeFactors_product ps.toFinset hprime
  rwa [trace_product_eq_finset w stop n v hp] at h

theorem trace_mass_eq_modulusCount (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (stop : List ℕ → Prop) (n : ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n (rootVertex z ∅ P mu) ∨ ps ∈ stopped w stop n (rootVertex z ∅ P mu)) :
    countMass Y small a (after w (rootVertex z ∅ P mu) ps) = (modulusCount Y small a ps.prod : ℝ) := by
  rw [root_after_mass,Finset.empty_union,modulusCount_eq_mass Y small a _ (suffixPrimes P ps),
    trace_primeFactors w stop n (rootVertex z ∅ P mu) hP hp]

end NumberTheoryLean.StoppedModulusCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_StrongReferenceTransport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StrongReferenceTransport
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferenceHistoryAdmission LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem strong_child_uncapped {w ell : ℝ} (hw : 1 < w) (hell : 0 ≤ ell) {z : Node}
    (hs : Valid z.side z.ratio) (hz : Consistent z) (p : ℕ) (hp : p.Prime)
    (hx : ell < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p))
    (ha : childAdmitted z.side z.gap (primeExponent w p)) : p ∈ uncappedChildren w ell z := by
  have hx0 : 0 < primeExponent w p := hell.trans_lt hx
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have hh : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact hh.le
    | true => simpa [capGuard,hcl] using hcap
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpLe := (exponent_le_iff hw hp0).mp hxp
  have hprime := Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff
    (Real.rpow_pos_of_pos (zero_lt_one.trans hw) z.cutoff).le).mpr hpLe,hp⟩
  apply Finset.mem_filter.mpr
  refine ⟨hprime,hx,hcap,?_⟩
  have hlo := cap_lower_ratio hs hz hx0 hcap
  cases hi : z.side with
  | even => exact hlo
  | odd =>
    rw [hi] at ha
    apply max_le
    · have h2 := (le_max_left (2*primeExponent w p) (primeExponent w p+2)).trans ha
      have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ hx0).mpr (by linarith)
      unfold childRatio
      linarith
    · exact hlo

theorem strong_child_state {w : ℝ} {z : Node} {p : ℕ} (hg : StrongState z)
    (hx : 0 < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p))
    (ha : childAdmitted z.side z.gap (primeExponent w p)) : StrongState (step w z p) := by
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have hh : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact hh.le
    | true => simpa [capGuard,hcl] using hcap
  cases hi : z.side with
  | even =>
    have hh := hg.2 hi
    constructor
    · change 2 ≤ z.gap-primeExponent w p
      linarith
    · simp [step,hi,Side.flip]
  | odd =>
    rw [hi] at ha
    have hh := (le_max_right (2*primeExponent w p) (primeExponent w p+2)).trans ha
    constructor
    · change 2 ≤ z.gap-primeExponent w p
      linarith
    · intro _hside
      exact hh

theorem strong_history_transport {w ell : ℝ} (hw : 1 < w) (hell : 0 ≤ ell)
    (z : Node) (ps : List ℕ) (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hD : ps.Pairwise (· > ·))
    (hP : ∀ p ∈ ps,p.Prime ∧ ell < primeExponent w p ∧ capGuard z.closed z.cutoff (primeExponent w p))
    (ha : admitted w z.side z.gap ps) : uncappedAllowed w ell z ps ∧ StrongState (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact ⟨trivial,hg⟩
  | cons p ps ih =>
    have hp := hP p (by simp)
    have hc := strong_child_uncapped hw hell hs hz p hp.1 hp.2.1 hp.2.2 ha.1
    have hone : uncappedAllowed w ell z [p] := ⟨hc,trivial⟩
    obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w ell z [p]).mp hone
    have hchild := ((allowed_cons w ell U z p []).mp hU).1
    have hr : 0 < z.gap := by linarith [hg.1]
    have hvalid := child_valid hs hchild
    have hcons := step_consistent hell hr hs hchild
    have hstrong := strong_child_state hg (hell.trans_lt hp.2.1) hp.2.2 ha.1
    have htailP : ∀ q ∈ ps,q.Prime ∧ ell < primeExponent w q ∧
        capGuard (step w z p).closed (step w z p).cutoff (primeExponent w q) := by
      intro q hq
      have hh := hP q (by simp [hq])
      refine ⟨hh.1,hh.2.1,?_⟩
      have hqp : q < p := (List.pairwise_cons.mp hD).1 q hq
      have hq0 : (0:ℝ)<q := by exact_mod_cast hh.1.pos
      have hqp' : (q:ℝ)<p := by exact_mod_cast hqp
      have hlog := Real.log_lt_log hq0 hqp'
      change primeExponent w q < primeExponent w p
      exact div_lt_div_of_pos_right hlog (Real.log_pos hw)
    have ht := ih (step w z p) hvalid hcons hstrong (List.pairwise_cons.mp hD).2 htailP ha.2
    exact ⟨⟨hc,ht.1⟩,ht.2⟩

theorem source_strong_state {B : ℝ} (hB : 3 ≤ B) (z : Node) (_hi : z.side=.even)
    (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B) : StrongState z := by
  have hr : 0 < z.ratio := by linarith
  have he := (eq_div_iff hr.ne').mp hz
  rw [hcut] at he
  have hm := mul_le_mul_of_nonneg_left h199 (show 0 ≤ B by linarith)
  constructor
  · nlinarith
  · intro _
    rw [hcut]
    nlinarith
end NumberTheoryLean.StrongReferenceTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_StrongSourceFamilies
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StrongSourceFamilies
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh StrongReferenceTransport
open ReferenceAdmission LogarithmicBinPartition UncappedCompactMass
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
attribute [local instance] Classical.propDecidable

theorem source_reference_transport {w top : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap) :
    ps ∈ uncappedPrefixes w 1 z ∧ 2 ≤ (terminal w z ps).gap := by
  obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hp
  have hDM := mem_decreasingPrefixes.mp hD
  have hP : ∀ p ∈ ps,p.Prime ∧ (1:ℝ)<primeExponent w p ∧
      capGuard z.closed z.cutoff (primeExponent w p) := by
    intro p hps
    obtain ⟨hpp,hlo,hhi⟩ := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hDM.2 p hps)
    have hpp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    refine ⟨hpp,?_,?_⟩
    · change 1 < Real.log p/Real.log w
      exact (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hlo)
    · have hx : primeExponent w p ≤ z.cutoff := (exponent_le_iff hw hpp0).mpr (by rwa [hcap])
      simpa only [capGuard,hclosed,ite_true, if_true] using hx
  have h := strong_history_transport hw (by norm_num : (0:ℝ)≤1) z ps hs hz hg hDM.1 hP ha
  exact ⟨(mem_uncappedPrefixes hw z ps).mpr h.1,h.2.1⟩

theorem finite_compact_family_le {w top K : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (F : Finset (List ℕ))
    (hF : F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hK : ∀ ps ∈ F,(terminal w z ps).gap ≤ K) :
    (∑ ps ∈ F,prefixWeight ps) ≤ compactPrefixMass K w 1 z := by
  have hsub : F ⊆ uncappedPrefixes w 1 z := fun ps hp =>
    (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hp)).1
  have he : (∑ ps ∈ F,prefixWeight ps)=
      ∑ ps ∈ F,prefixWeight ps*(if 2 ≤ (terminal w z ps).gap ∧ (terminal w z ps).gap ≤ K then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ps hp
    have hlo := (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hp)).2
    rw [ite_eq_left ⟨hlo,hK ps hp⟩,mul_one]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ps _ _ => by
    split_ifs
    · simpa only [mul_one] using prefixWeight_nonneg ps
    · simp)

theorem uniform_source_family_mass (K d : ℝ) (hK : 3 ≤ K) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      w < top → Real.log B ≤ d*Real.log w → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ K) → B^2*(∑ ps ∈ F,prefixWeight ps) ≤ C := by
  obtain ⟨C,B₀,w₀,hC,_hB₀,hw₀,hbound⟩ := uniform_uncapped_compact_mass K 1 d hK (by norm_num) hd
  refine ⟨C,max 3 B₀,w₀,hC,le_max_left _ _,hw₀,?_⟩
  intro B w top hB hw htop hcomp z hi h199 h23 hz hcut hclosed hcap F hF hFK
  have hB3 : 3 ≤ B := (le_max_left _ _).trans hB
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hwm : 1 < w := hw₀.trans_le hw
  have hmass := finite_compact_family_le hwm htop z hs hz hg hclosed (by rwa [hcut]) F hF hFK
  exact (mul_le_mul_of_nonneg_left hmass (sq_nonneg B)).trans
    (hbound B w ((le_max_right _ _).trans hB) hw hcomp z hi h199 h23 hz hcut)
end NumberTheoryLean.StrongSourceFamilies

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SourcePrimeProductData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourcePrimeProductData
open FinitePathGeometry PrimeHistories ReferenceAdmission LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

theorem source_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (ps : List ℕ)
    (hd : ps.Pairwise (· > ·)) (hp : ∀ p∈ps,p ∈ sourcePrimeSet w top) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  have hn : ps.Nodup := hd.imp (fun h => ne_of_gt h)
  have hprime : ∀ p∈ps,p.Prime := fun p h => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p h)).1
  have hpos : 0 < ps.prod := List.prod_pos (fun p h => (hprime p h).pos)
  have he : (∏ p∈ps.toFinset,p)=ps.prod := by simpa using List.prod_toFinset (fun p : ℕ => p) hn
  have hprimeF : ∀ p∈ps.toFinset,p.Prime := fun p h => hprime p (List.mem_toFinset.mp h)
  have hsq : Squarefree (∏ p∈ps.toFinset,p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpp q hqq hpq
      simp only [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprimeF p hpp) (hprimeF q hqq)).mpr hpq
    · intro p hpp
      exact (hprimeF p hpp).squarefree
  have hfac : ps.prod.primeFactors=ps.toFinset := by
    rw [← he]
    exact ErdosInverseCounts.primeFactors_product ps.toFinset hprimeF
  refine ⟨hpos,by rwa [he] at hsq,?_⟩
  intro p hpf
  rw [hfac] at hpf
  exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p (List.mem_toFinset.mp hpf))).2.1

theorem reference_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (i : Side) (r : ℝ) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) i r) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  classical
  have hh := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  exact source_word_product_data hw htop ps hh.1 hh.2
end NumberTheoryLean.SourcePrimeProductData


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ReferenceExponentialTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceExponentialTail
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh ReferenceAdmission StrongReferenceTransport StrongSourceFamilies
open LiteralUniformPrimeTail LiteralPrimeOccupation LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem uniform_reference_exponential_tail (d c eps : ℝ) (hd : 0 < d) (hc : 0 < c) (heps : 0 < eps) :
    ∃ K₀ B₀ w₀ : ℝ,3 ≤ K₀ ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ K B w top : ℝ,K₀ ≤ K → B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,K < (terminal w z ps).gap) →
      B^2*(∑ ps∈F,prefixWeight ps*Real.exp (-c*(terminal w z ps).gap)) ≤ eps := by
  obtain ⟨M,BT,WT,_hBT,hWT,hTail⟩ := actual_uniform_original_prime_tail d c eps hd hc heps
  refine ⟨3*((M:ℝ)+1),max BT 3,WT,by nlinarith [Nat.cast_nonneg (α:=ℝ) M],le_max_right _ _,hWT,?_⟩
  intro K B w top hK hB hw₀ htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF hGap
  have hB3 : 3 ≤ B := (le_max_right _ _).trans hB
  have hw : 1 < w := hWT.trans_le hw₀
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hsub : F ⊆ uncappedPrefixes w 1 z :=
    fun ps hps => (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hps)).1
  have hsum : (∑ ps∈F,prefixWeight ps*Real.exp (-c*(terminal w z ps).gap))=
      ∑ ps∈F,prefixWeight ps*tailListReward c (3*((M:ℝ)+1)) w z ps := by
    apply Finset.sum_congr rfl
    intro ps hps
    rw [tailListReward,ite_eq_left (hK.trans_lt (hGap ps hps))]
  rw [hsum]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ps _ _ => mul_nonneg (prefixWeight_nonneg ps) (tailListReward_nonneg c (3*((M:ℝ)+1)) w z ps))
  exact (mul_le_mul_of_nonneg_left hle (sq_nonneg B)).trans
    (hTail M le_rfl B w ((le_max_left _ _).trans hB) hw₀ 1 (by norm_num) (by linarith)
      hcomp z hi h199 h23 hz hcut)
end NumberTheoryLean.ReferenceExponentialTail


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LargeGapCountErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ActualCountErrorMass
open ErdosInverseCounts ActualCountErrorEdges
open ErdosPrimeInputs.PrimePrefixMass


theorem count_error_identity (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d : ℕ) (hd : 0 < d) :
    |(modulusCount Y small a d:ℝ)-((Y:ℝ)/(d:ℝ))*V0|=
      ((Y:ℝ)/(d:ℝ))*V0*|relativeCountError Y small a V0 d| := by
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have hmu : 0 < ((Y:ℝ)/(d:ℝ))*V0 := by positivity
  have he : (modulusCount Y small a d:ℝ)-((Y:ℝ)/(d:ℝ))*V0=
      (((Y:ℝ)/(d:ℝ))*V0)*relativeCountError Y small a V0 d := by
    unfold relativeCountError
    field_simp [hmu.ne']
  rw [he,abs_mul,abs_of_pos hmu]

theorem word_count_error_weight (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (ps : List ℕ) (hd : 0 < ps.prod) :
    |(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|=
      ((Y:ℝ)*V0)*(prefixWeight ps*|wordCountError Y small a V0 ps|) := by
  rw [count_error_identity Y small a V0 hY hV ps.prod hd,StoppedVertexHistory.prefixWeight_product]
  unfold wordCountError
  ring

theorem finite_count_error_weight (B : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (F : Finset (List ℕ)) (hF : ∀ ps∈F,0 < ps.prod) :
    (B^2/((Y:ℝ)*V0))*(∑ ps∈F,|(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|)=
      B^2*(∑ ps∈F,prefixWeight ps*|wordCountError Y small a V0 ps|) := by
  have he := Finset.sum_congr rfl (fun ps hp => word_count_error_weight Y small a V0 hY hV ps (hF ps hp))
  rw [he,← Finset.mul_sum]
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp [hYr,hV.ne']
end NumberTheoryLean.ActualCountErrorMass



namespace NumberTheoryLean.CountErrorClassification
open PrimeHistories ActualCountErrorEdges ErdosInverseCounts

attribute [local instance] Classical.propDecidable

theorem error_sum_partition (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) :
    errorSum Y small a V0 F=
      errorSum Y small a V0 (largeGapWords w K z F)+
      errorSum Y small a V0 (smallErrorWords w K eps Y small a V0 z F)+
      errorSum Y small a V0 (badCompactWords w K eps Y small a V0 z F) := by
  simp only [errorSum,largeGapWords,smallErrorWords,badCompactWords,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps _hp
  by_cases hgap : K<(terminal w z ps).gap
  · simp [hgap,not_le_of_gt hgap]
  · have hg : (terminal w z ps).gap ≤ K := le_of_not_gt hgap
    by_cases he : |wordCountError Y small a V0 ps| ≤ eps
    · simp [hgap,hg,he,not_lt_of_ge he]
    · simp [hgap,hg,he,lt_of_not_ge he]
end NumberTheoryLean.CountErrorClassification



namespace NumberTheoryLean.LiteralCountErrorLedger
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open StoppedModulusCount FlatStoppedIdentity ReferenceAdmission ErdosInverseCounts StoppedTraceAdmission

attribute [local instance] Classical.propDecidable

theorem negative_abs_le_signed (k : ℕ) (x : ℝ) : -|x| ≤ (-1:ℝ)^k*x := by
  have hh := neg_abs_le ((-1:ℝ)^k*x)
  simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hh

theorem literal_count_error_ledger (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (residue : ℕ → ℕ)
    (z : Node) (V0 : ℝ) (stop : List ℕ → Prop) (hi : z.side=.even) (hP : ∀ p∈P,p.Prime) :
    ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap +
      (∑ ps∈stopped w stop P.card (rootVertex z ∅ P ((Y:ℝ)*V0)),
        (countSurvivors Y small residue (after w (rootVertex z ∅ P ((Y:ℝ)*V0)) ps)-
          referenceValue w (after w (rootVertex z ∅ P ((Y:ℝ)*V0)) ps))) -
      (∑ ps∈expanded w stop P.card (rootVertex z ∅ P ((Y:ℝ)*V0)),
        |(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤
      countSurvivors Y small residue (rootVertex z ∅ P ((Y:ℝ)*V0)) := by
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  have hRaw := actual_reference_error_lower_bound w Y small residue stop P.card v le_rfl hi
  have hErr : -(∑ ps∈expanded w stop P.card v,
      |(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤
      ∑ ps∈expanded w stop P.card v,(-1:ℝ)^ps.length*(countMass Y small residue (after w v ps)-(after w v ps).scale) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ps hps
    rw [trace_mass_eq_modulusCount w Y small P residue z ((Y:ℝ)*V0) stop P.card hP (Or.inl hps),after_scale_product]
    change -|(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0| ≤
      (-1:ℝ)^ps.length*((modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)*V0)/(ps.prod:ℝ))
    have he : ((Y:ℝ)*V0)/(ps.prod:ℝ)=((Y:ℝ)/(ps.prod:ℝ))*V0 := by ring
    rw [he]
    exact negative_abs_le_signed ps.length _
  change ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap+_+_ ≤ _ at hRaw
  change ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap+_-_ ≤ _
  linarith

theorem expanded_reference_subset (w : ℝ) (P : Finset ℕ) (z : Node) (V : ℝ) (stop : List ℕ → Prop) (n : ℕ) :
    expanded w stop n (rootVertex z ∅ P V) ⊆ referencePrefixes w P z.side z.gap := by
  intro ps hps
  exact trace_reference_member w stop n (rootVertex z ∅ P V) (Or.inl hps)
end NumberTheoryLean.LiteralCountErrorLedger



namespace NumberTheoryLean.CountErrorFamilyMajorant
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongReferenceTransport StrongSourceFamilies
open ReferenceCountEnvelope ActualCountErrorMass ActualCountErrorEdges SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem count_error_family_majorant (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧ ∀ B w top : ℝ,3 ≤ B → w₀ ≤ w → w < top →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ C*(B^2*(∑ ps∈F,prefixWeight ps)) := by
  obtain ⟨C,W,hC,hW,hEnvelope⟩ := reference_count_envelope_jb247 aStar ha
  refine ⟨C,max W 2,hC,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop Y hY z hroot hi h199 hz hcut hclosed hpower residue F hF
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hErr : ∀ ps∈F,|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤ C := by
    intro ps hps
    have hh := hEnvelope B w top hB ((le_max_left _ _).trans hw₀) htop Y hY z hroot hi h199 hz hcut hclosed hpower residue ps (hF hps)
    have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hps)).2
    have he : Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact hh.trans ((mul_le_mul_of_nonneg_left he hC.le).trans_eq (mul_one C))
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have hsum : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ C*(∑ ps∈F,prefixWeight ps) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hps
    have hh := mul_le_mul_of_nonneg_left (hErr ps hps) (prefixWeight_nonneg ps)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg B)
  nlinarith
end NumberTheoryLean.CountErrorFamilyMajorant



namespace NumberTheoryLean.LargeGapCountErrors
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open ReferenceCountEnvelope ReferenceExponentialTail ActualCountErrorMass ActualCountErrorEdges SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem uniform_large_gap_count_errors (aStar d eps : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heps : 0 < eps) :
    ∃ K₀ B₀ w₀ : ℝ,3 ≤ K₀ ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ K B w top : ℝ,K₀ ≤ K → B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,K < (terminal w z ps).gap) →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ eps := by
  obtain ⟨C,WE,hC,hWE,hEnvelope⟩ := reference_count_envelope_jb247 aStar ha
  obtain ⟨K₀,B₀,WT,hK₀,hB₀,hWT,hTail⟩ := uniform_reference_exponential_tail d (1/192) (eps/C) hd (by norm_num) (by positivity)
  refine ⟨K₀,B₀,max WE (max WT 2),hK₀,hB₀,hWE.trans_le (le_max_left _ _),?_⟩
  intro K B w top hK hB hw₀ htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue F hF hGap
  have hw : 1 < w := hWE.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have hErr : ∀ ps∈F,|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤
      C*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) := by
    intro ps hps
    exact hEnvelope B w top (hB₀.trans hB) ((le_max_left _ _).trans hw₀) htop Y hY z hroot hi h199 hz hcut hclosed hpower residue ps (hF hps)
  have hsum : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ C*(∑ ps∈F,prefixWeight ps*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hps
    have hh := mul_le_mul_of_nonneg_left (hErr ps hps) (prefixWeight_nonneg ps)
    nlinarith
  have htail := hTail K B w top hK hB ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀)
    htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF hGap
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg B)
  have ht := mul_le_mul_of_nonneg_left htail hC.le
  have he : C*(eps/C)=eps := mul_div_cancel₀ eps hC.ne'
  rw [he] at ht
  nlinarith
end NumberTheoryLean.LargeGapCountErrors


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CompactSmallCountErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CompactSmallCountErrors
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongSourceFamilies
open ActualCountErrorEdges ActualCountErrorMass SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem uniform_compact_small_count_errors (K d : ℝ) (hK : 3 ≤ K) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      w < top → Real.log B ≤ d*Real.log w → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ Y : ℕ,0 < Y → ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,(terminal w z ps).gap ≤ K ∧
        |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤ eps) →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ C*eps := by
  obtain ⟨C,B₀,W,hC,hB₀,hW,hMass⟩ := uniform_source_family_mass K d hK hd
  refine ⟨C,B₀,max W 2,hC,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop hcomp z hi h199 h23 hz hcut hclosed hpower Y hY residue eps heps F hF hGood
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have he : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ (∑ ps∈F,prefixWeight ps)*eps := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ps hps
    exact mul_le_mul_of_nonneg_left (hGood ps hps).2 (prefixWeight_nonneg ps)
  have hsum := hMass B w top hB ((le_max_left _ _).trans hw₀) htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF
    (fun ps hps => (hGood ps hps).1)
  have hh := mul_le_mul_of_nonneg_left he (sq_nonneg B)
  have hc := mul_le_mul_of_nonneg_right hsum heps
  nlinarith
end NumberTheoryLean.CompactSmallCountErrors


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CountErrorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CountErrorRemainder
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open CountErrorClassification LargeGapCountErrors CompactSmallCountErrors CountErrorFamilyMajorant
open LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem uniform_count_error_remainder (aStar d eta : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heta : 0 < eta) :
    ∃ Cbad K₀ : ℝ,0 < Cbad ∧ 3 ≤ K₀ ∧ ∀ K : ℝ,K₀ ≤ K →
      ∃ Csmall B₀ w₀ : ℝ,0 < Csmall ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      (B^2/((Y:ℝ)*V0))*errorSum Y small residue V0 F ≤ eta+Csmall*eps+
        Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z F,prefixWeight ps)) := by
  obtain ⟨Cbad,WD,hCbad,hWD,hDiscard⟩ := count_error_family_majorant aStar ha
  obtain ⟨K₀,BG,WG,hK₀,hBG,hWG,hLarge⟩ := uniform_large_gap_count_errors aStar d eta ha hd heta
  refine ⟨Cbad,K₀,hCbad,hK₀,?_⟩
  intro K hK
  obtain ⟨Csmall,BC,WC,hCsmall,hBC,hWC,hCompact⟩ := uniform_compact_small_count_errors K d (hK₀.trans hK) hd
  refine ⟨Csmall,max BG BC,max WG (max WC WD),hCsmall,hBG.trans (le_max_left _ _),hWG.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue eps heps F hF
  dsimp only
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  have hB3 : 3 ≤ B := hBG.trans ((le_max_left _ _).trans hB)
  have hA := hLarge K B w top hK ((le_max_left _ _).trans hB) ((le_max_left _ _).trans hw) htop hcomp
    Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue (largeGapWords w K z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1) (fun ps hp => (Finset.mem_filter.mp hp).2)
  have hBnd := hCompact B w top ((le_max_right _ _).trans hB) ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw)
    htop hcomp z hi h199 h23 hz hcut hclosed hpower Y hY residue eps heps
    (smallErrorWords w K eps Y small residue V0 z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1) (fun ps hp => (Finset.mem_filter.mp hp).2)
  have hD := hDiscard B w top hB3 ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw) htop
    Y hY z hroot hi h199 hz hcut hclosed hpower residue (badCompactWords w K eps Y small residue V0 z F)
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
  have hPart := congrArg (fun t : ℝ => (B^2/((Y:ℝ)*V0))*t) (error_sum_partition w K eps Y small residue V0 z F)
  unfold errorSum at hPart ⊢
  change (B^2/((Y:ℝ)*V0))*(∑ ps∈F,|(ErdosInverseCounts.modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤ _
  nlinarith
end NumberTheoryLean.CountErrorRemainder


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_StoppedErrorReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StoppedErrorReduction
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open CountErrorRemainder CountErrorClassification LiteralCountErrorLedger
open StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem stopped_error_reduction_jb247_oai (aStar d eta : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heta : 0 < eta) :
    ∃ Cbad K₀ : ℝ,0 < Cbad ∧ 3 ≤ K₀ ∧ ∀ K : ℝ,K₀ ≤ K →
      ∃ Csmall B₀ w₀ : ℝ,0 < Csmall ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ eps : ℝ,0 ≤ eps → ∀ stop : List ℕ → Prop,
      let P := sourcePrimeSet w top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let v := rootVertex z ∅ P ((Y:ℝ)*V0)
      B^2*referencePolynomial w P z.side z.gap+
        (B^2/((Y:ℝ)*V0))*(∑ ps∈stopped w stop P.card v,
          (countSurvivors Y small residue (after w v ps)-referenceValue w (after w v ps))) -
        eta-Csmall*eps-Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z (expanded w stop P.card v),prefixWeight ps)) ≤
        (B^2/((Y:ℝ)*V0))*countSurvivors Y small residue v := by
  obtain ⟨Cbad,K₀,hCbad,hK₀,hReduction⟩ := uniform_count_error_remainder aStar d eta ha hd heta
  refine ⟨Cbad,K₀,hCbad,hK₀,?_⟩
  intro K hK
  obtain ⟨Csmall,B₀,W,hCsmall,hB₀,hW,hError⟩ := hReduction K hK
  refine ⟨Csmall,B₀,max W 2,hCsmall,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue eps heps stop
  dsimp only
  let P := sourcePrimeSet w top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < V0 := (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hmu : 0 < (Y:ℝ)*V0 := mul_pos hYr hV
  have hErrorBound := hError B w top hB ((le_max_left _ _).trans hw₀) htop hcomp Y hY z hroot
    hi h199 h23 hz hcut hclosed hpower residue eps heps (expanded w stop P.card v)
    (expanded_reference_subset w P z ((Y:ℝ)*V0) stop P.card)
  have hPrime : ∀ p∈P,p.Prime := fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp).1
  have hLedger := literal_count_error_ledger w Y small P residue z V0 stop hi hPrime
  have hScaled := mul_le_mul_of_nonneg_left hLedger (show 0 ≤ B^2/((Y:ℝ)*V0) by positivity)
  have hCancel : (B^2/((Y:ℝ)*V0))*(((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap)=
      B^2*referencePolynomial w P z.side z.gap := by field_simp [hmu.ne']
  dsimp only at hErrorBound
  unfold errorSum at hErrorBound
  change B^2*referencePolynomial w P z.side z.gap+
    (B^2/((Y:ℝ)*V0))*(∑ ps∈stopped w stop P.card v,
      (countSurvivors Y small residue (after w v ps)-referenceValue w (after w v ps))) -
    eta-Csmall*eps-Cbad*(B^2*(∑ ps∈badCompactWords w K eps Y small residue V0 z (expanded w stop P.card v),prefixWeight ps)) ≤
    (B^2/((Y:ℝ)*V0))*countSurvivors Y small residue v
  nlinarith
end NumberTheoryLean.StoppedErrorReduction


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247_oai := @OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247_oai
