-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:16.836802+00:00
-- url     : https://prove2.me/submissions/c3f186f4-53b8-4566-9216-1f898941a741

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
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RetainedOccupationLimit_retained_original_occupation_limit_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

end NumberTheoryLean.FinitePathGeometry



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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

end NumberTheoryLean.PrimeHistories

end

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

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RepresentativeStopGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeStopGeometry

open NumberTheoryLean.ReferenceAdmission

theorem sourceHeight_mono {x y : ℝ} (hxy : x ≤ y) : sourceHeight x ≤ sourceHeight y := by
  exact max_le_max (by linarith) (by linarith)

theorem sourceHeight_error {x y d : ℝ} (hxy : |x-y| ≤ d) : sourceHeight x ≤ sourceHeight y+2*d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hxy
  apply max_le
  · have hy := le_max_left (2*y) (y+2)
    change 2*y ≤ sourceHeight y at hy
    linarith [(abs_le.mp hxy).2]
  · have hy := le_max_right (2*y) (y+2)
    change y+2 ≤ sourceHeight y at hy
    linarith [(abs_le.mp hxy).2]

theorem representative_safety_admits {r rrep x xrep Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hx : x ≤ xrep) (hr : rrep ≤ r)
    (hsafe : sourceHeight xrep+3*Delta ≤ rrep) : sourceHeight x ≤ r := by
  have hH := sourceHeight_mono hx
  linarith

theorem regular_margin_to_representative {r rrep x xrep Delta h : ℝ}
    (hr : |rrep-r| ≤ Delta) (hx : |xrep-x| ≤ h)
    (hsmall : 2*h ≤ 6*Delta) (hmargin : sourceHeight x+10*Delta < r) :
    sourceHeight xrep+3*Delta < rrep := by
  have hH := sourceHeight_error hx
  linarith [(abs_le.mp hr).1]

end NumberTheoryLean.RepresentativeStopGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepresentativeAdmission
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeAdmission

open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeStopGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_gap_sum (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = z.gap-(ps.map (primeExponent w)).sum := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    rw [terminal_cons,ih,List.map_cons,List.sum_cons]
    change z.gap-primeExponent w p-(ps.map (primeExponent w)).sum = _
    ring

theorem representativeGap_le_actual (w : ℝ) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ)
    (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p) :
    representativeGap rep z.gap ps ≤ (terminal w z ps).gap := by
  have hs : (ps.map (primeExponent w)).sum ≤ (ps.map rep).sum := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hrep p (by simp)) (ih (fun q hq => hrep q (by simp [hq])))
  rw [terminal_gap_sum]
  exact sub_le_sub_left hs z.gap

theorem admitted_of_even_prefix_safety (w : ℝ) (z : Node) (ps : List ℕ)
    (hsafe : ∀ pre : List ℕ,∀ p : ℕ,∀ tail : List ℕ,ps = pre++p::tail →
      (terminal w z (pre++[p])).side = .even →
      sourceHeight (primeExponent w p) ≤ (terminal w z (pre++[p])).gap) :
    admitted w z.side z.gap ps := by
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
    constructor
    · cases hi : z.side with
      | even => trivial
      | odd =>
        have h := hsafe [] p ps rfl (by simp [terminal,step,hi,Side.flip])
        exact h
    · apply ih (step w z p)
      intro pre q tail htail hside
      have he : p::ps = (p::pre)++q::tail := by rw [List.cons_append,htail]
      have h := hsafe (p::pre) q tail he (by simpa only [List.cons_append,terminal_cons] using hside)
      simpa only [List.cons_append,terminal_cons] using h

theorem representative_safety_preserves_admission (w : ℝ) (rep : ℕ → ℝ)
    (z : Node) (ps : List ℕ) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p)
    (hsafe : ∀ pre : List ℕ,∀ p : ℕ,∀ tail : List ℕ,ps = pre++p::tail →
      (terminal w z (pre++[p])).side = .even →
      sourceHeight (rep p)+3*Delta ≤ representativeGap rep z.gap (pre++[p])) :
    admitted w z.side z.gap ps := by
  apply admitted_of_even_prefix_safety w z ps
  intro pre p tail heq hside
  have hsub : ∀ q ∈ pre++[p],q ∈ ps := by
    intro q hq
    rw [heq]
    simp only [List.mem_append,List.mem_cons] at hq ⊢
    tauto
  have hg := representativeGap_le_actual w rep z (pre++[p]) (fun q hq => hrep q (hsub q hq))
  have hx : primeExponent w p ≤ rep p := hrep p (hsub p (by simp))
  exact representative_safety_admits hDelta hx hg (hsafe pre p tail heq hside)

end NumberTheoryLean.RepresentativeAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRepresentatives
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinRepresentatives

open ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure
open PrimeHistories RepresentativeAdmission

theorem bin_exponent_bounds {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    leftExponent w R < primeExponent w p ∧ primeExponent w p ≤ rightExponent w R xi := by
  obtain ⟨hprime,hlo,hhi⟩ := (mem_primeBin hR.le hxi p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  exact ⟨div_lt_div_of_pos_right (Real.log_lt_log hR hlo) (Real.log_pos hw),
    div_le_div_of_nonneg_right (Real.log_le_log hp0 hhi) (Real.log_pos hw).le⟩

theorem bin_exponent_width {w R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    rightExponent w R xi-leftExponent w R = Real.log (1+xi)/Real.log w := by
  rw [rightExponent,leftExponent,Real.log_mul (by positivity : (1+xi:ℝ) ≠ 0) hR.ne']
  ring

theorem representative_error {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    0 ≤ rightExponent w R xi-primeExponent w p ∧
      rightExponent w R xi-primeExponent w p ≤ xi/Real.log w := by
  have h := bin_exponent_bounds hw hR hxi hp
  have hlog : Real.log (1+xi) ≤ xi := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+xi)
    linarith
  refine ⟨sub_nonneg.mpr h.2,?_⟩
  calc
    _ ≤ rightExponent w R xi-leftExponent w R := by linarith [h.1]
    _ = Real.log (1+xi)/Real.log w := bin_exponent_width hR hxi
    _ ≤ _ := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le

theorem finite_gap_movement (w : ℝ) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ) {h : ℝ}
    (hrep : ∀ p ∈ ps,0 ≤ rep p-primeExponent w p ∧ rep p-primeExponent w p ≤ h) :
    0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
      (terminal w z ps).gap-representativeGap rep z.gap ps ≤ (ps.length:ℝ)*h := by
  have hs : 0 ≤ (ps.map rep).sum-(ps.map (primeExponent w)).sum ∧
      (ps.map rep).sum-(ps.map (primeExponent w)).sum ≤ (ps.length:ℝ)*h := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp := hrep p (by simp)
      have ht := ih (fun q hq => hrep q (by simp [hq]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      constructor <;> linarith
  rw [terminal_gap_sum,representativeGap]
  constructor <;> linarith

theorem source_movement_bound {w B Clen xi : ℝ} (hw : 1 < w) (hC : 0 ≤ Clen) (hxi : 0 ≤ xi)
    (hcomp : Real.log B ≤ 2*Real.log w) (rep : ℕ → ℝ) (z : Node) (ps : List ℕ)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hrep : ∀ p ∈ ps,0 ≤ rep p-primeExponent w p ∧ rep p-primeExponent w p ≤ xi/Real.log w) :
    0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
      (terminal w z ps).gap-representativeGap rep z.gap ps ≤ 2*Clen*xi := by
  have hm := finite_gap_movement w rep z ps hrep
  have hlog := Real.log_pos hw
  refine ⟨hm.1,hm.2.trans ?_⟩
  calc
    _ ≤ (Clen*Real.log B)*(xi/Real.log w) :=
      mul_le_mul_of_nonneg_right hlen (div_nonneg hxi hlog.le)
    _ ≤ (Clen*(2*Real.log w))*(xi/Real.log w) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) (div_nonneg hxi hlog.le)
    _ = _ := by field_simp [hlog.ne']

end NumberTheoryLean.PrimeBinRepresentatives

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



namespace NumberTheoryLean.StoppedVertexHistory

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex ReferenceForestTelescoping ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass

theorem prefixWeight_product (ps : List ℕ) : prefixWeight ps = ((ps.prod:ℕ):ℝ)⁻¹ := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    change (p:ℝ)⁻¹*prefixWeight ps = ((p*ps.prod:ℕ):ℝ)⁻¹
    rw [ih,Nat.cast_mul,mul_inv_rev]
    ring

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.SourceStopPredicate

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeAdmission RepresentativeStopGeometry
open PrimeBinRepresentatives ActualSourceTags ActualBinOwners FiniteFirstTag
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem finite_safe_admits (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ)
    (hDelta : 0 ≤ Delta) (hrep : ∀ p ∈ ps,primeExponent w p ≤ rep p)
    (hs : representativeSafe w rep z Delta ps) : admitted w z.side z.gap ps := by
  apply representative_safety_preserves_admission w rep z ps hDelta hrep
  intro pre p tail heq hside
  have hmem : pre++[p] ∈ ps.inits := by
    apply (List.mem_inits _ _).mpr
    exact ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using heq.symm⟩
  have h := hs (pre++[p]) hmem (by simp) hside
  rwa [List.getLastD_concat] at h

end NumberTheoryLean.SourceStopPredicate



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCandidateFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeTraceInvariance
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate

theorem terminal_side_length (w : ℝ) (z z' : Node) (ps qs : List ℕ)
    (hz : z.side = z'.side) (hlen : ps.length = qs.length) :
    (terminal w z ps).side = (terminal w z' qs).side := by
  induction ps generalizing qs z z' with
  | nil =>
    have hq : qs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst qs
    exact hz
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      apply ih (step w z p) (step w z' q) qs
      · change z.side.flip = z'.side.flip
        rw [hz]
      · simpa using hlen

theorem representative_last_eq (rep : ℕ → ℝ) (ps qs : List ℕ)
    (hm : ps.map rep = qs.map rep) : rep (ps.getLastD 0) = rep (qs.getLastD 0) := by
  induction ps generalizing qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hm.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hm
    | cons q qs =>
      have hh := List.cons.inj hm
      cases ps with
      | nil =>
        have hq : qs = [] := List.map_eq_nil_iff.mp hh.2.symm
        subst qs
        exact hh.1
      | cons r rs =>
        cases qs with
        | nil => simp at hh
        | cons s ss =>
          simpa using ih (s::ss) hh.2

theorem representativeSafe_map_iff (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeSafe w rep z Delta ps ↔ representativeSafe w rep z Delta qs := by
  have forward (ps qs : List ℕ) (hm : ps.map rep = qs.map rep)
      (hs : representativeSafe w rep z Delta ps) : representativeSafe w rep z Delta qs := by
    intro pre hpre hne hside
    obtain ⟨tail,htail⟩ := (List.mem_inits pre qs).mp hpre
    have hlen : ps.length = qs.length := by simpa using congrArg List.length hm
    have hk : pre.length ≤ ps.length := by rw [← htail,List.length_append] at hlen; omega
    have hm' : (ps.take pre.length).map rep = pre.map rep := by
      rw [List.map_take,hm,← htail,List.map_append,List.take_append]
      simp
    have hprefix : ps.take pre.length ∈ ps.inits :=
      (List.mem_inits _ _).mpr ⟨ps.drop pre.length,List.take_append_drop _ _⟩
    have hlen' : (ps.take pre.length).length = pre.length := by
      rw [List.length_take,Nat.min_eq_left hk]
    have hne' : ps.take pre.length ≠ [] := by
      intro he
      have : pre.length = 0 := by rw [he] at hlen'; simpa using hlen'.symm
      exact hne (List.length_eq_zero_iff.mp this)
    have hside' : (terminal w z (ps.take pre.length)).side = .even :=
      (terminal_side_length w z z _ _ rfl hlen').trans hside
    have hh := hs (ps.take pre.length) hprefix hne' hside'
    have he := representative_last_eq rep _ _ hm'
    simpa only [representativeGap,hm',he] using hh
  exact ⟨forward ps qs hm,forward qs ps hm.symm⟩

end NumberTheoryLean.RepresentativeTraceInvariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LogarithmicBinScale


theorem logWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < logWidth w z xi :=
  div_pos (span_log_pos hw hwz) (by exact_mod_cast binCount_pos hw hwz hxi)

theorem count_mul_logWidth {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    (binCount w z xi:ℝ)*logWidth w z xi = Real.log (z/w) := by
  have hn : (binCount w z xi:ℝ) ≠ 0 := by exact_mod_cast (binCount_pos hw hwz hxi).ne'
  unfold logWidth
  field_simp [hn]

theorem logWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    logWidth w z xi ≤ Real.log (1+xi) := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.le_ceil (Real.log (z/w)/Real.log (1+xi))
  have hm := (div_le_iff₀ hlog).mp hc
  change Real.log (z/w) ≤ (binCount w z xi:ℝ)*Real.log (1+xi) at hm
  apply (div_le_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  exact (by nlinarith : Real.log (z/w) ≤ Real.log (1+xi)*(binCount w z xi:ℝ))

theorem effectiveWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < effectiveWidth w z xi := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (logWidth_pos hw hwz hxi))

theorem effectiveWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    effectiveWidth w z xi ≤ xi := by
  have he := Real.exp_le_exp.mpr (logWidth_le hw hwz hxi)
  rw [Real.exp_log (by linarith : 0 < 1+xi)] at he
  exact sub_le_iff_le_add.mpr (by linarith)

end NumberTheoryLean.LogarithmicBinScale



namespace NumberTheoryLean.LogarithmicBinEndpoints

open LogarithmicBinScale PrimeBinRepresentatives ErdosInversePrimeBin

theorem endpoint_zero (w z xi : ℝ) : endpoint w z xi 0 = w := by simp [endpoint]

theorem upper_endpoint (w z xi : ℝ) (i : Fin (binCount w z xi)) :
    upper w z xi i = endpoint w z xi (i.1+1) := by
  simp only [upper,width,lower,effectiveWidth,endpoint,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.exp_add]
  ring

theorem endpoint_count {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    endpoint w z xi (binCount w z xi) = z := by
  rw [endpoint,count_mul_logWidth hw hwz hxi,Real.exp_log (div_pos (hw.trans hwz) hw)]
  field_simp [hw.ne']

theorem endpoint_pos {w z xi : ℝ} (hw : 0 < w) (k : ℕ) : 0 < endpoint w z xi k := by
  exact mul_pos hw (Real.exp_pos _)

theorem endpoint_mono {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {k m : ℕ} (hkm : k ≤ m) : endpoint w z xi k ≤ endpoint w z xi m := by
  have hc : (k:ℝ) ≤ m := by exact_mod_cast hkm
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (logWidth_pos hw hwz hxi).le)) hw.le

theorem bin_source_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) : w ≤ lower w z xi i ∧ lower w z xi i < upper w z xi i ∧
      upper w z xi i ≤ z := by
  have hlow : w ≤ lower w z xi i := by
    have h := endpoint_mono hw hwz hxi (Nat.zero_le i.1)
    simpa only [endpoint_zero,lower] using h
  have hstrict : lower w z xi i < upper w z xi i := by
    have hp : 0 < lower w z xi i := endpoint_pos hw _
    have he : 0 < width w z xi i := effectiveWidth_pos hw hwz hxi
    unfold upper
    nlinarith
  refine ⟨hlow,hstrict,?_⟩
  rw [upper_endpoint]
  exact (endpoint_mono hw hwz hxi (Nat.succ_le_of_lt i.isLt)).trans_eq (endpoint_count hw hwz hxi)

theorem bins_separated {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i j : Fin (binCount w z xi)) (hij : i ≠ j) :
    upper w z xi i ≤ lower w z xi j ∨ upper w z xi j ≤ lower w z xi i := by
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Or.inl
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)
  · apply Or.inr
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)

theorem bin_prime_in_source {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) {p : ℕ} (hp : p ∈ primeBin (lower w z xi i) (width w z xi i)) :
    p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  have hb := (mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
  have hs := bin_source_bounds hw hwz hxi i
  exact ⟨hb.1,hs.1.trans_lt hb.2.1,hb.2.2.trans hs.2.2⟩

end NumberTheoryLean.LogarithmicBinEndpoints



namespace NumberTheoryLean.LogarithmicBinLabels

open LogarithmicBinScale LogarithmicBinEndpoints ErdosInversePrimeBin

theorem coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    0 < coordinate w z xi p ∧ coordinate w z xi p ≤ (binCount w z xi:ℝ) := by
  have hlog : 0 < Real.log ((p:ℝ)/w) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hp.1)
  have hd := logWidth_pos hw hwz hxi
  refine ⟨div_pos hlog hd,?_⟩
  apply (div_le_iff₀ hd).mpr
  rw [count_mul_logWidth hw hwz hxi]
  exact Real.log_le_log (div_pos (hw.trans hp.1) hw) (div_le_div_of_nonneg_right hp.2 hw.le)

theorem index_eq_ceiling {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) : index w z xi p = ⌈coordinate w z xi p⌉₊-1 := by
  have hc : ⌈coordinate w z xi p⌉₊ ≤ binCount w z xi := Nat.ceil_le.mpr (coordinate_bounds hw hwz hxi hp).2
  exact min_eq_right (by omega)

theorem label_coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    ((label hw hwz hxi p).1:ℝ) < coordinate w z xi p ∧
      coordinate w z xi p ≤ ((label hw hwz hxi p).1:ℝ)+1 := by
  have hc := coordinate_bounds hw hwz hxi hp
  have hpos : 0 < ⌈coordinate w z xi p⌉₊ := Nat.ceil_pos.mpr hc.1
  have hlow := Nat.ceil_lt_add_one hc.1.le
  have hhigh := Nat.le_ceil (coordinate w z xi p)
  have he : ((label hw hwz hxi p).1:ℝ) = (⌈coordinate w z xi p⌉₊:ℝ)-1 := by
    change (index w z xi p:ℝ) = _
    rw [index_eq_ceiling hw hwz hxi hp,Nat.cast_sub (by omega : 1 ≤ ⌈coordinate w z xi p⌉₊)]
    norm_num
  rw [he]
  constructor <;> linarith

theorem label_value_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    lower w z xi (label hw hwz hxi p) < (p:ℝ) ∧
      (p:ℝ) ≤ upper w z xi (label hw hwz hxi p) := by
  have hb := label_coordinate_bounds hw hwz hxi hp
  have hd := logWidth_pos hw hwz hxi
  have hpw : 0 < (p:ℝ)/w := div_pos (hw.trans hp.1) hw
  have he : coordinate w z xi p*logWidth w z xi = Real.log ((p:ℝ)/w) := by
    unfold coordinate
    field_simp [hd.ne']
  have hlo := mul_lt_mul_of_pos_right hb.1 hd
  have hhi := mul_le_mul_of_nonneg_right hb.2 hd.le
  rw [he] at hlo hhi
  have hExpLo := Real.exp_lt_exp.mpr hlo
  have hExpHi := Real.exp_le_exp.mpr hhi
  rw [Real.exp_log hpw] at hExpLo hExpHi
  constructor
  · have h := (lt_div_iff₀ hw).mp hExpLo
    simpa only [lower,endpoint,mul_comm] using h
  · rw [upper_endpoint]
    have h := (div_le_iff₀ hw).mp hExpHi
    simpa only [endpoint,Nat.cast_add,Nat.cast_one,mul_comm] using h

theorem label_prime_membership {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hprime : p.Prime) (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    p ∈ primeBin (lower w z xi (label hw hwz hxi p)) (width w z xi (label hw hwz hxi p)) := by
  apply (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mpr
  exact ⟨hprime,(label_value_bounds hw hwz hxi hp).1,(label_value_bounds hw hwz hxi hp).2⟩

end NumberTheoryLean.LogarithmicBinLabels



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

theorem bin_mem_iff_label {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) (p : ℕ) :
    p ∈ primeBin (lower w z xi i) (width w z xi i) ↔
      p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z ∧ label hw hwz hxi p = i := by
  constructor
  · intro hp
    have hs := bin_prime_in_source hw hwz hxi i hp
    have hI := (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
    have hL := label_value_bounds hw hwz hxi hs.2
    refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    by_contra hne
    have hsep := bins_separated hw hwz hxi i (label hw hwz hxi p) (Ne.symm hne)
    have huI : (p:ℝ) ≤ upper w z xi i := hI.2.2
    have hlI : lower w z xi i < (p:ℝ) := hI.2.1
    rcases hsep with hsep | hsep <;> linarith [hlI,hL.1,hL.2]
  · rintro ⟨hprime,hlo,hhi,heq⟩
    rw [← heq]
    exact label_prime_membership hw hwz hxi hprime ⟨hlo,hhi⟩

theorem bins_pairwise_disjoint {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i j : Fin (binCount w z xi)) (hij : i ≠ j) :
    Disjoint (primeBin (lower w z xi i) (width w z xi i))
      (primeBin (lower w z xi j) (width w z xi j)) := by
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have hpi := (bin_mem_iff_label hw hwz hxi i p).mp hi
  have hpj := (bin_mem_iff_label hw hwz hxi j p).mp hj
  exact hij (hpi.2.2.2.symm.trans hpj.2.2.2)

end NumberTheoryLean.LogarithmicBinPartition



namespace NumberTheoryLean.LogarithmicBinMaps

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SourceStopPredicate PrimeBinRepresentatives RepresentativeAdmission PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_list_boxed {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (ps : List ℕ) (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w z) :
    boxed (lower w z xi) (width w z xi) (label hw hwz hxi) ps := by
  intro p hps
  have hs := (mem_sourcePrimeSet hw hwz p).mp (hp p hps)
  exact label_prime_membership hw hwz hxi hs.1 hs.2

theorem source_representative_error {w z xi : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w z) :
    0 ≤ representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ∧
      representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ≤ xi/Real.log w := by
  have hw0 : 0 < w := by linarith
  have hs := (mem_sourcePrimeSet hw0 hwz p).mp hp
  have hbin := label_prime_membership hw0 hwz hxi hs.1 hs.2
  have he := representative_error hw (endpoint_pos hw0 _) (effectiveWidth_pos hw0 hwz hxi).le hbin
  refine ⟨he.1,he.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (effectiveWidth_le hw0 hwz hxi) (Real.log_pos hw).le

theorem source_prefix_movement {w z xi B Clen : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (v : Node) (ps : List ℕ)
    (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w z) (hlen : (ps.length:ℝ) ≤ Clen*Real.log B) :
    0 ≤ (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ∧
    (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ≤ 2*Clen*xi := by
  exact source_movement_bound hw hC hxi.le hcomp _ v ps hlen
    (fun p hps => source_representative_error hw hwz hxi (hp p hps))

end NumberTheoryLean.LogarithmicBinMaps



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
open SuccessfulTailTransport ExponentialMesh LowStateHorizon
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceMarkedStopping
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedPrefixTools
open FinitePathGeometry PrimeHistories FiniteFirstTag ActualSourceTags PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_cutoff_last (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [terminal_append]
  rfl

theorem terminal_lastD (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLastD 0) := by
  have hh := terminal_cutoff_last w z ps hne
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rwa [he]

end NumberTheoryLean.MarkedPrefixTools

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ActualCofactorCellData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem mem_selections {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) :
    f ∈ selections P m ↔ ∀ i, f i ⊆ P i ∧ (f i).card = m i := by
  simp only [selections, Fintype.mem_piFinset, Finset.mem_powersetCard]

theorem selection_disjoint {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    Pairwise (fun i j => Disjoint (f i) (f j)) := by
  intro i j hij
  exact (hd hij).mono (hf i) (hf j)

theorem selectionProduct_eq_union {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    selectionProduct f = ∏ p ∈ selectionPrimes f, p := by
  symm
  exact Finset.prod_biUnion (fun i _ j _ hij => selection_disjoint P hd f hf hij)

theorem recover_bin {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) (i : ι) :
    selectionPrimes f ∩ P i = f i := by
  ext p
  constructor
  · intro hp
    obtain ⟨hu, hpi⟩ := Finset.mem_inter.mp hp
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hu
    by_cases hji : j = i
    · simpa only [hji] using hpj
    · exact False.elim ((Finset.disjoint_left.mp (hd hji)) (hf j hpj) hpi)
  · intro hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩, hf i hp⟩

end ErdosCofactorChoices

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteBoxWordMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosSubsetWord
open ErdosCofactorChoices

attribute [local instance] Classical.decEq

theorem mem_descendingWord {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) (p : ℕ) :
    p ∈ descendingWord f ↔ ∃ i,p ∈ f i := by
  simp [descendingWord,selectionPrimes]

theorem descendingWord_nodup {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).Nodup := Finset.sort_nodup _ _

theorem descendingWord_strict {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).Pairwise (· > ·) := (Finset.sortedGT_sort _).pairwise

theorem descendingWord_toFinset {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).toFinset=selectionPrimes f := Finset.sort_toFinset _ _

theorem descendingWord_length {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (mult : ι → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f : ι → Finset ℕ)
    (hf : f ∈ selections P mult) : (descendingWord f).length=∑ i,mult i := by
  have hmem := (mem_selections P mult f).mp hf
  rw [descendingWord,Finset.length_sort,selectionPrimes,Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => (hmem i).2)
  · intro i _ j _ hij
    exact selection_disjoint P hd f (fun b => (hmem b).1) hij

theorem descendingWord_product {ι : Type*} [Fintype ι] (P : ι → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f : ι → Finset ℕ)
    (hf : ∀ i,f i ⊆ P i) : (descendingWord f).prod=selectionProduct f := by
  rw [selectionProduct_eq_union P hd f hf,← descendingWord_toFinset]
  simpa only [List.map_id'] using (List.prod_toFinset (fun p : ℕ => p) (descendingWord_nodup f)).symm

end ErdosSubsetWord



namespace ErdosSearchCount
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean ActualSourceTags

attribute [local instance] Classical.propDecidable

theorem selectedCount_eq_sum (P : ℕ → Bool) (ps : List ℕ) :
    selectedCount P ps=(ps.map (fun p => if P p then (1:ℕ) else 0)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases he : P p <;> simp [selectedCount,he] at * <;> omega

end ErdosSearchCount



namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosSearchCount ErdosTagEvent
open NumberTheoryLean ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem selected_prime_label {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (b : Fin (binCount w top xi))
    {p : ℕ} (hp : p ∈ f b) : label (zero_lt_one.trans hw) htop hxi p=b := by
  have hmem := ((mem_selections _ mult f).mp hf b).1 hp
  exact ((bin_mem_iff_label (zero_lt_one.trans hw) htop hxi b p).mp hmem).2.2.2

theorem global_word_length {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) : (descendingWord f).length=∑ b,mult b :=
  descendingWord_length _ mult
    (fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij) f hf

theorem word_source_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    ∀ p ∈ descendingWord f,p ∈ sourcePrimeSet w top := by
  intro p hp
  obtain ⟨b,hb⟩ := (mem_descendingWord f p).mp hp
  have hbin := ((mem_selections _ mult f).mp hf b).1 hb
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    (bin_prime_in_source (zero_lt_one.trans hw) htop hxi b hbin)

end ErdosSubsetWord



namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosSearchCount
open NumberTheoryLean
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem global_label_mono {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top) (hqp : q ≤ p) :
    label (zero_lt_one.trans hw) htop hxi q ≤ label (zero_lt_one.trans hw) htop hxi p := by
  have hpb := label_value_bounds (zero_lt_one.trans hw) htop hxi ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp).2
  have hqb := label_value_bounds (zero_lt_one.trans hw) htop hxi ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp hq).2
  by_contra hn
  have hlt : label (zero_lt_one.trans hw) htop hxi p < label (zero_lt_one.trans hw) htop hxi q := lt_of_not_ge hn
  have he : upper w top xi (label (zero_lt_one.trans hw) htop hxi p) ≤
      lower w top xi (label (zero_lt_one.trans hw) htop hxi q) := by
    rw [upper_endpoint]
    exact endpoint_mono (zero_lt_one.trans hw) htop hxi (Nat.succ_le_of_lt hlt)
  have hreal : (q:ℝ) ≤ p := by exact_mod_cast hqp
  linarith

theorem word_label_count {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (b : Fin (binCount w top xi)) :
    ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).count b=mult b := by
  have hmem := (mem_selections _ mult f).mp hf
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [List.count_eq_countP,List.countP_map,List.countP_eq_length_filter]
  change selectedCount (fun p => label (zero_lt_one.trans hw) htop hxi p == b) (descendingWord f)=mult b
  rw [selectedCount_eq_sum,← List.sum_toFinset _ (descendingWord_nodup f),
    descendingWord_toFinset,selectionPrimes,Finset.sum_biUnion]
  · calc
      _ = ∑ i,if i=b then mult i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ _p ∈ f i,if i=b then (1:ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hl := selected_prime_label hw htop hxi mult f hf i hp
            simp [hl]
          _ = _ := by split_ifs <;> simp [(hmem i).2]
      _ = _ := by simp
  · intro i _ j _ hij
    exact selection_disjoint _ hd f (fun i => (hmem i).1) hij

theorem word_labels_ordered {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  apply (descendingWord_strict f).imp_of_mem
  intro p q hp hq hpq
  exact global_label_mono hw htop hxi (word_source_membership hw htop hxi mult f hf p hp)
    (word_source_membership hw htop hxi mult f hf q hq) hpq.le

theorem selection_label_word_eq {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (hg : g ∈ selections (globalBins w top xi) mult) :
    (descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)=
      (descendingWord g).map (label (zero_lt_one.trans hw) htop hxi) := by
  have hp : ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).Perm
      ((descendingWord g).map (label (zero_lt_one.trans hw) htop hxi)) := by
    apply List.perm_iff_count.mpr
    intro b
    rw [word_label_count hw htop hxi mult f hf,word_label_count hw htop hxi mult g hg]
  exact List.Perm.eq_of_pairwise' (word_labels_ordered hw htop hxi mult f hf)
    (word_labels_ordered hw htop hxi mult g hg) hp

end ErdosSubsetWord



namespace NumberTheoryLean.FiniteBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord CanonicalSubsetBox
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem word_injective {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f g : Fin n → Finset ℕ)
    (hf : ∀ i,f i ⊆ P i) (hg : ∀ i,g i ⊆ P i) (he : descendingWord f=descendingWord g) : f=g := by
  have hu : selectionPrimes f=selectionPrimes g := by
    rw [← descendingWord_toFinset f,← descendingWord_toFinset g,he]
  funext i
  rw [← recover_bin P hd f hf i,← recover_bin P hd g hg i,hu]

theorem wordBox_mass {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (∑ ps ∈ wordBox P mult,prefixWeight ps)=selectionMass P mult := by
  rw [wordBox,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    rw [StoppedVertexHistory.prefixWeight_product,
      descendingWord_product P hd f (fun i => ((mem_selections P mult f).mp hf i).1)]
  · intro f hf g hg he
    exact word_injective P hd f g (fun i => ((mem_selections P mult f).mp hf i).1)
      (fun i => ((mem_selections P mult g).mp hg i).1) he

theorem wordBoxes_disjoint {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (mult mult' : Fin n → ℕ) (hne : mult ≠ mult') :
    Disjoint (wordBox P mult) (wordBox P mult') := by
  apply Finset.disjoint_left.mpr
  intro ps hp hp'
  obtain ⟨f,hf,hef⟩ := Finset.mem_image.mp hp
  obtain ⟨g,hg,heg⟩ := Finset.mem_image.mp hp'
  have hfP := (mem_selections P mult f).mp hf
  have hgP := (mem_selections P mult' g).mp hg
  have he := word_injective P hd f g (fun i => (hfP i).1) (fun i => (hgP i).1) (hef.trans heg.symm)
  subst g
  apply hne
  funext i
  exact (hfP i).2.symm.trans (hgP i).2

theorem total_box_mass_eq {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (M : Finset (Fin n → ℕ)) :
    (∑ mult ∈ M,selectionMass P mult) = ∑ ps ∈ boxWords P M,prefixWeight ps := by
  rw [boxWords,Finset.sum_biUnion (fun i _ j _ hij => wordBoxes_disjoint P hd i j hij)]
  apply Finset.sum_congr rfl
  intro mult _hm
  exact (wordBox_mass P mult hd).symm
end NumberTheoryLean.FiniteBoxWordMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualSafeBoxMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SafeSubsetBoxGeometry
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeTraceInvariance
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ReferenceAdmission ErdosCofactorChoices ErdosSubsetWord
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem selection_representatives_eq {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (hg : g ∈ selections (globalBins w top xi) mult) :
    (descendingWord f).map (representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi))=
      (descendingWord g).map (representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)) := by
  have hh := congrArg (List.map (fun b => PrimeBinRepresentatives.rightExponent w (lower w top xi b) (width w top xi b)))
    (selection_label_word_eq hw htop hxi mult f g hf hg)
  unfold representative
  simpa only [List.map_map,Function.comp_def] using hh

theorem anchored_choice_geometry {w top xi B Clen K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (mult : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi Clen B K z mult)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) mult) :
    descendingWord f ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap ∧
      (terminal w z (descendingWord f)).gap ≤ K+2*Clen*xi := by
  obtain ⟨g,hg,hlen,hSafe,hK⟩ := hanchor
  let rep := representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
  have he := selection_representatives_eq hw htop hxi mult f g hf hg
  have hsf : representativeSafe w rep z (2*Clen*xi) (descendingWord f) :=
    (representativeSafe_map_iff w rep z (2*Clen*xi) _ _ he).mpr hSafe
  have hsource := word_source_membership hw htop hxi mult f hf
  have hsourceg := word_source_membership hw htop hxi mult g hg
  have hadmit : admitted w z.side z.gap (descendingWord f) := by
    apply finite_safe_admits w rep z (2*Clen*xi) _ (by positivity) _ hsf
    intro p hp
    have hh := (source_representative_error hw htop hxi (hsource p hp)).1
    change 0 ≤ rep p-primeExponent w p at hh
    linarith
  refine ⟨Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨descendingWord_strict f,hsource⟩,hadmit⟩,?_⟩
  have hlength : (descendingWord f).length=(descendingWord g).length :=
    (global_word_length hw htop hxi mult f hf).trans (global_word_length hw htop hxi mult g hg).symm
  have hlenf : ((descendingWord f).length:ℝ) ≤ Clen*Real.log B := by rwa [hlength]
  have hmf := source_prefix_movement hw htop hxi hC hcomp z (descendingWord f) hsource hlenf
  have hmg := source_prefix_movement hw htop hxi hC hcomp z (descendingWord g) hsourceg hlen
  have hgap : representativeGap rep z.gap (descendingWord f)=representativeGap rep z.gap (descendingWord g) := by
    unfold representativeGap
    rw [he]
  change 0 ≤ (terminal w z (descendingWord f)).gap-representativeGap rep z.gap (descendingWord f) ∧
    (terminal w z (descendingWord f)).gap-representativeGap rep z.gap (descendingWord f) ≤ 2*Clen*xi at hmf
  change 0 ≤ (terminal w z (descendingWord g)).gap-representativeGap rep z.gap (descendingWord g) ∧
    (terminal w z (descendingWord g)).gap-representativeGap rep z.gap (descendingWord g) ≤ 2*Clen*xi at hmg
  rw [hgap] at hmf
  linarith [hmf.2,hmg.1]
end NumberTheoryLean.SafeSubsetBoxGeometry



namespace NumberTheoryLean.ActualSafeBoxMass
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open LogarithmicBinScale LogarithmicBinPartition ReferenceAdmission StrongSourceFamilies
open SafeSubsetBoxGeometry FiniteBoxWordMass CanonicalSubsetBox ErdosSubsetWord

attribute [local instance] Classical.propDecidable

theorem uniform_safe_box_mass (K : ℝ) (hK : 3 ≤ K) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ (hw : 1 < w) (htop : w < top) (xi Clen : ℝ) (hxi : 0 < xi),0 ≤ Clen →
      Real.log B ≤ 2*Real.log w → 2*Clen*xi ≤ 1 → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ M : Finset (Fin (binCount w top xi) → ℕ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen B K z mult) →
      B^2*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult) ≤ C := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,hbound⟩ := uniform_source_family_mass (K+1) 2 (by linarith) (by norm_num)
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w top hB hw hw1 htop xi Clen hxi hClen hcomp hsmall z hi h199 h23 hz hcut hclosed hcap M hanchors
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw1) htop hxi i j hij
  let F := boxWords (globalBins w top xi) M
  have hF : F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
    intro ps hps
    obtain ⟨mult,hm,hword⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hword
    have hh := (anchored_choice_geometry hw1 htop hxi hClen hcomp z mult (hanchors mult hm) f hf).1
    rwa [he] at hh
  have hFK : ∀ ps ∈ F,(terminal w z ps).gap ≤ K+1 := by
    intro ps hps
    obtain ⟨mult,hm,hword⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hword
    have hh := (anchored_choice_geometry hw1 htop hxi hClen hcomp z mult (hanchors mult hm) f hf).2
    rw [he] at hh
    linarith
  rw [total_box_mass_eq (globalBins w top xi) hd M]
  exact hbound B w top hB hw htop hcomp z hi h199 h23 hz hcut hclosed hcap F hF hFK
end NumberTheoryLean.ActualSafeBoxMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualWordSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualWordSelection
open FinitePathGeometry PrimeHistories SourceStopPredicate
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosCofactorChoices ErdosSubsetWord

attribute [local instance] Classical.propDecidable

theorem wordSelection_mem {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    wordSelection (label (zero_lt_one.trans hw) htop hxi) ps ∈ selections (globalBins w top xi)
      (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) := by
  apply (mem_selections _ _ _).mpr
  intro b
  refine ⟨?_,rfl⟩
  intro p hp
  obtain ⟨hp,hb⟩ := Finset.mem_filter.mp hp
  have hh := source_list_boxed (zero_lt_one.trans hw) htop hxi ps hsource p (List.mem_toFinset.mp hp)
  simpa only [globalBins,hb] using hh

theorem wordSelection_recovers {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ)
    (hd : ps.Pairwise (· > ·)) : descendingWord (wordSelection lab ps)=ps := by
  apply (descendingWord_strict _).eq_of_mem_iff hd
  intro p
  simp only [mem_descendingWord,wordSelection,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨b,hp,_hb⟩
    exact hp
  · intro hp
    exact ⟨lab p,hp,rfl⟩

end NumberTheoryLean.ActualWordSelection


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualPrefixClearance
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualPrefixClearance
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open MarkedPrefixTools ErdosPrimeInputs.HarmonicPrimeMeasure


theorem clearance_supplies_safety {w top xi Clen B : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi))
    (z : Node) (ps : List ℕ) (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hclear : actualClearance w z (2*Clen*xi) ps) :
    representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) ps := by
  intro qs hqs hne hside
  have hpre := (List.mem_inits _ _).mp hqs
  have hsrc : ∀ p ∈ qs,p ∈ sourcePrimeSet w top := fun p hp => hsource p (hpre.subset hp)
  have hlenq : (qs.length:ℝ) ≤ Clen*Real.log B :=
    (by exact_mod_cast hpre.length_le : (qs.length:ℝ) ≤ ps.length).trans hlen
  have hlast : qs.getLastD 0 ∈ qs := by
    have he : qs.getLastD 0=qs.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hx := source_representative_error hw htop hxi (hsrc _ hlast)
  rw [← terminal_lastD w z qs hne] at hx
  have hr := source_prefix_movement hw htop hxi hC hcomp z qs hsrc hlenq
  have hxa := abs_of_nonneg hx.1
  apply le_of_lt
  apply regular_margin_to_representative (Delta := 2*Clen*xi) (h := xi/Real.log w)
  · rw [abs_sub_comm,abs_of_nonneg hr.1]
    exact hr.2
  · rw [hxa]
    exact hx.2
  · exact hsmall
  · exact hclear qs hqs hne hside

end NumberTheoryLean.ActualPrefixClearance


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RegularityDefectPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualRegularBoxes
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualPrefixClearance ActualWordSelection
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SafeSubsetBoxGeometry ErdosSubsetWord ErdosCofactorChoices ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem regular_word_anchor {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) :
    SafeAnchor hw htop hxi Clen B K z (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) := by
  obtain ⟨hd,hlen,hclear,hgap,_hsingle⟩ := Finset.mem_filter.mp hp
  have hm := mem_decreasingPrefixes.mp hd
  refine ⟨wordSelection (label (zero_lt_one.trans hw) htop hxi) ps,
    wordSelection_mem hw htop hxi ps hm.2,?_⟩
  rw [wordSelection_recovers _ ps hm.1]
  exact ⟨hlen,clearance_supplies_safety hw htop hxi hC hcomp hsmall z ps hm.2 hlen hclear,hgap⟩

theorem regular_boxes_anchors {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) :
    ∀ mult ∈ regularBoxes hw htop hxi Clen B K z,SafeAnchor hw htop hxi Clen B K z mult := by
  intro mult hm
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  exact regular_word_anchor hw htop hxi hC hcomp hsmall z ps hps

end NumberTheoryLean.ActualRegularBoxes



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BinCutGapMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricBoxImages
open PrimeHistories ActualWordSelection ActualRegularBoxes GeometricRegularWords
open SafeSubsetBoxGeometry ErdosSubsetWord LogarithmicBinScale LogarithmicBinLabels
attribute [local instance] Classical.propDecidable

theorem geometric_boxes_subset {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) :
    geometricBoxes hw htop hxi C B R L alpha beta z ⊆ regularBoxes hw htop hxi C B R z := by
  intro mult hm
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr ⟨ps,(Finset.mem_filter.mp hps).1,rfl⟩

theorem geometric_box_anchor {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi)) (z : Node) :
    ∀ mult ∈ geometricBoxes hw htop hxi C B R L alpha beta z,SafeAnchor hw htop hxi C B R z mult := by
  intro mult hm
  exact regular_boxes_anchors hw htop hxi hC hcomp hsmall z mult (geometric_boxes_subset hw htop hxi z hm)

end NumberTheoryLean.GeometricBoxImages



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricTotalBoxMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricTotalBoxMass
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualSafeBoxMass
open GeometricBoxImages SafeSubsetBoxGeometry CanonicalSubsetBox FilteredBoxWordMass
open LogarithmicBinScale ErdosSubsetWord


theorem uniform_geometric_box_mass_jb247_oai (K : ℝ) (hK : 3 ≤ K) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ (hw : 1 < w) (htop : w < top),
    ∀ xi Clen : ℝ,∀ hxi : 0 < xi,1 ≤ Clen → Real.log B ≤ 2*Real.log w → 2*Clen*xi ≤ 1 →
    ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z →
      z.cutoff=B → z.closed=true → w^B=top → ∀ L alpha beta : ℝ,
    B^2*(∑ m∈geometricBoxes hw htop hxi Clen B K L alpha beta z,selectionMass (globalBins w top xi) m) ≤ C := by
  obtain ⟨C,B₀,W,hC,hB₀,hW,hTotal⟩ := uniform_safe_box_mass K hK
  refine ⟨C,B₀,max W (Real.exp 1),hC,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi Clen hxi hClen hcomp hsmall z hi h199 h23 hz hcut hclosed hpower L alpha beta
  have hlog : 1 ≤ Real.log w := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hw₀)
    simpa only [Real.log_exp] using hh
  have hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  exact hTotal B w top hB ((le_max_left _ _).trans hw₀) hw htop xi Clen hxi
    (by linarith) hcomp hsmall z hi h199 h23 hz hcut hclosed hpower
    (geometricBoxes hw htop hxi Clen B K L alpha beta z)
    (geometric_box_anchor hw htop hxi (by linarith) hcomp hmesh z)

end NumberTheoryLean.GeometricTotalBoxMass


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247_oai := @OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247_oai
