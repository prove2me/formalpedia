-- Prove2me | solution 1 for OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:14.373612+00:00
-- url     : https://prove2.me/submissions/ab032ab1-44c7-414c-8c93-82afc559657f

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
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
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_ErdosContinuousAnomaly_common_anomaly_exponential_jb247
import Theorems.Thm_OAI_Erdos970_ErdosCorrectionLimit_compact_limiting_integral_tendsto_jb247
import Theorems.Thm_OAI_Erdos970_ErdosCorrectionLimit_full_limiting_integral_eq_jb247
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightFutureIntegrals
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem future_integral_of_mass {a b : ℝ → ℝ} {base : ℝ} (hbase : 1 ≤ base)
    (ha : ContinuousOn a (Ioi 0))
    (hb : ∀ t, base - 1 < t → 0 ≤ b t)
    (hd : ∀ t, base < t → HasDerivAt (fun u => u * a u) (-b (t - 1)) t)
    (hl : Tendsto (fun t => t * a t) atTop (𝓝 0))
    {s : ℝ} (hs : base ≤ s) :
    IntegrableOn b (Ioi (s - 1)) ∧ s * a s = ∫ t in Ioi (s - 1), b t := by
  let H : ℝ → ℝ := fun t => (t + 1) * a (t + 1)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : 0 < base) hs
  have hc : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hm : ContinuousAt (fun t => t * a t) s :=
      continuousAt_id.mul (ha.continuousAt (Ioi_mem_nhds hs0))
    have hm' : ContinuousAt (fun t => t * a t) ((s - 1) + 1) := by simpa only [sub_add_cancel] using hm
    have hc' := hm'.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      ((continuous_id.add continuous_const : Continuous (fun t : ℝ => t + 1)).continuousAt)
    convert! hc'.continuousWithinAt using 1
    all_goals try with_reducible_and_instances rfl
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-b t) t := by
    intro t ht
    have hdt := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! hdt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hnonpos : ∀ t ∈ Ioi (s - 1), -b t ≤ 0 := by
    intro t ht
    exact neg_nonpos.mpr (hb t (by change s - 1 < t at ht; linarith))
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc hder hnonpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc hder hnonpos hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem lowerDeficit_nonneg (s : ℝ) : 0 ≤ lowerDeficit s := by
  by_cases hs : 1 ≤ s
  · exact (deficits_pos hs).1.le
  · simp only [lowerDeficit, f_initial sieveA (by linarith : s ≤ 2), sub_zero, zero_le_one]

theorem lower_future_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn upperDeficit (Ioi (s - 1)) ∧
      s * lowerDeficit s = ∫ t in Ioi (s - 1), upperDeficit t := by
  exact future_integral_of_mass (a := lowerDeficit) (b := upperDeficit) (base := 2) (by norm_num)
    lowerDeficit_continuous.continuousOn (fun t ht => (deficits_pos (s := t) (by linarith)).2.le)
    (fun _ ht => lowerDeficit_mass_deriv ht) lowerDeficit_mass_tendsto_zero hs

theorem upper_future_integral {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn lowerDeficit (Ioi (s - 1)) ∧
      s * upperDeficit s = ∫ t in Ioi (s - 1), lowerDeficit t := by
  exact future_integral_of_mass (a := upperDeficit) (b := lowerDeficit) (base := 1) le_rfl
    ((F_continuousOn sieveA).sub continuousOn_const) (fun t _ => lowerDeficit_nonneg t)
    (fun _ ht => upperDeficit_mass_deriv_of_one_lt ht) upperDeficit_mass_tendsto_zero hs

end NumberTheoryLean.DeficitFutureIntegrals

end

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

theorem cost_pos {t : ℝ} (ht : 0 < t) : 0 < cost t := by
  unfold cost
  exact Real.log_pos (by have h : 0 < 1 / t := one_div_pos.mpr ht; linarith)

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


section

open _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem upperCutoff_bounds (i : Side) (r b : ℝ) : 1 ≤ upperCutoff i r b ∧ upperCutoff i r b ≤ 2 := by
  cases i
  · exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_left _ _).trans (min_le_left _ _))⟩

theorem upperCutoff_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => upperCutoff i p.1 p.2) := by
  cases i <;> unfold upperCutoff <;> fun_prop

theorem upperCutoff_odd_small {r b : ℝ} (hr : r ≤ 4) : upperCutoff .odd r b=1 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

end ErdosContinuousBoundary

end


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_VariableUpperIntegral
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary

theorem continuous_variable_upper_integral
    (F : (ℝ×ℝ) → ℝ → ℝ) (hF : Continuous F.uncurry)
    (c : (ℝ×ℝ) → ℝ) (hc : Continuous c) :
    Continuous (fun p => ∫ x in (1:ℝ)..c p,F p x) := by
  let G : (ℝ×ℝ) → ℝ → ℝ := fun p t => F p ((c p-1)*t+1)
  have hG : Continuous G.uncurry := by
    change Continuous (F.uncurry ∘ (fun q : (ℝ×ℝ)×ℝ => (q.1,(c q.1-1)*q.2+1)))
    apply hF.comp
    exact continuous_fst.prodMk
      (((hc.comp continuous_fst).sub continuous_const).mul continuous_snd |>.add continuous_const)
  have hi : Continuous (fun p => ∫ t in Icc (0:ℝ) 1,G p t) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have heq (p : ℝ×ℝ) : (c p-1)*(∫ t in Icc (0:ℝ) 1,G p t)=∫ x in (1:ℝ)..c p,F p x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a:=0) (b:=1) (fun x => F p x) (c p-1) 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc] at h
    simpa only [smul_eq_mul,mul_zero,zero_add,mul_one,sub_add_cancel,G] using h
  exact ((hc.sub continuous_const).mul hi).congr heq

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryGateSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_continuous (n : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryTerm n i p.1 p.2) := by
  induction n generalizing i with
  | zero => exact continuous_const
  | succ n ih =>
    let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => boundaryTerm n i.flip (p.1-x) x/(max 1 x)
    have hchild : Continuous (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) :=
      (ih i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
    have hden : Continuous (fun q : (ℝ×ℝ)×ℝ => (max 1 q.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun q => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 q.2)))
    have hF : Continuous F.uncurry := by
      have he : F.uncurry = (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) *
          (fun q => (max 1 q.2)⁻¹) := by
        funext ⟨p,x⟩
        exact div_eq_mul_inv _ _
      rw [he]
      exact hchild.mul hden
    exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem boundaryTerm_odd_small (n : ℕ) {r b : ℝ} (hr : r ≤ 4) :
    boundaryTerm (n+1) .odd r b=0 := by
  rw [boundaryTerm,upperCutoff_odd_small hr,intervalIntegral.integral_same]

theorem boundaryTerm_depth_zero (n : ℕ) (i : Side) {r b : ℝ} (hr : r ≤ (n:ℝ)+1) :
    boundaryTerm (n+2) i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact boundaryTerm_odd_small 1 (by norm_num at hr <;> linarith)
    | even =>
      rw [boundaryTerm]
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only [Side.flip]
          rw [boundaryTerm_odd_small 0 (by norm_num at hr <;> linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,boundaryTerm]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr <;> linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousReference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_zero_of_index (n : ℕ) (hn : 2 ≤ n) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)-1) : boundaryTerm n i r b=0 := by
  have he : n=(n-2)+2 := by omega
  rw [he]
  apply boundaryTerm_depth_zero
  have hc : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
  linarith

theorem truncatedReference_stable {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (i : Side) {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    truncatedReference N i r b=truncatedReference M i r b := by
  unfold truncatedReference
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n _hnM hnN
  have hNn : N ≤ n := le_of_not_gt (by simpa only [Finset.mem_range] using hnN)
  have hrn : r ≤ (n:ℝ)-1 := hr.trans (sub_le_sub_right (by exact_mod_cast hNn) 1)
  rw [boundaryTerm_zero_of_index n (hN.trans hNn) i hrn,mul_zero]

theorem referenceDepth_bounds (r : ℝ) : 2 ≤ referenceDepth r ∧ r ≤ (referenceDepth r : ℝ)-1 := by
  have h := Nat.le_ceil (max r 0)
  have hr : r ≤ max r 0 := le_max_left _ _
  unfold referenceDepth
  constructor
  · omega
  · push_cast
    linarith

theorem boundaryReference_eq_truncated (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : boundaryReference i r b=truncatedReference N i r b := by
  unfold boundaryReference
  rcases le_total (referenceDepth r) N with h | h
  · exact truncatedReference_stable (referenceDepth_bounds r).1 h i (referenceDepth_bounds r).2
  · exact (truncatedReference_stable hN h i hr).symm

theorem truncatedReference_continuous (N : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => truncatedReference N i p.1 p.2) := by
  apply continuous_finsetSum
  intro n _hn
  exact continuous_const.mul (boundaryTerm_continuous n i)

theorem boundaryReference_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryReference i p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let N := referenceDepth (p.1+1)
  have hc := (truncatedReference_continuous N i).continuousAt (x:=p)
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ q : ℝ×ℝ in 𝓝 p,q.1 < p.1+1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1+1))
  filter_upwards [he] with q hq
  exact boundaryReference_eq_truncated N (referenceDepth_bounds (p.1+1)).1 i
    (hq.le.trans (referenceDepth_bounds (p.1+1)).2)

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_WeightedAnomalyConvergence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open _root_.Erdos970.MeasureTheory _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceBenchmarkDecay NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

theorem continuousAnomaly_continuousOn (i : Side) : ContinuousOn (continuousAnomaly i) (Ici 2) := by
  intro r hr
  have hq : ContinuousAt (fun x : ℝ => boundaryReference i x 2) r :=
    ((boundaryReference_continuous i).comp (continuous_id.prodMk continuous_const)).continuousAt
  have hb : ContinuousAt (fun x : ℝ => benchmark i (x/2)) r := by
    cases i with
    | even => exact (f_continuous sieveA).continuousAt.comp (continuousAt_id.div_const 2)
    | odd =>
      have hx : r/2 ≠ 0 := by have h := hr; change 2 ≤ r at h; linarith
      have hg : ContinuousAt (fun x : ℝ => x/2) r := continuousAt_id.div_const 2
      have hF : ContinuousAt (F sieveA) ((fun x : ℝ => x/2) r) := F_continuousAt sieveA hx
      simpa only [Function.comp_def,benchmark] using hF.comp (f := fun x : ℝ => x/2) hg
  exact (hq.sub (continuousAt_const.mul hb)).continuousWithinAt

end ErdosContinuousAnomaly

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InvariantFiniteness
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantDensities
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

theorem oddFactor_bounds {s : ℝ} (hs : 1 ≤ s) : 0 ≤ oddFactor s ∧ oddFactor s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  have hinv : 1 / s ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hs0)).mpr hsq
  have hnonneg : 0 ≤ 1 / s ^ 2 := by positivity
  unfold oddFactor
  constructor <;> linarith

theorem oddFactor_measurable : Measurable oddFactor := by
  unfold oddFactor
  fun_prop

theorem evenDensity_measurable : Measurable evenDensity :=
  phiEven_measurable.indicator measurableSet_Ici

theorem evenDensity_nonneg (s : ℝ) : 0 ≤ evenDensity s := by
  by_cases hs : 2 ≤ s
  · rw [evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact (phiEven_pos (by linarith)).le
  · rw [evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs)]

theorem oddDensity_nonneg (s : ℝ) : 0 ≤ oddDensity s := by
  by_cases hs : 1 ≤ s
  · rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · rw [oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs)]

end Erdos970Dependency.InvariantDensities

end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantFiniteness
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.InvariantDensities

theorem integrableOn_Ici_of_exp_tail {f : ℝ → ℝ} {a : ℝ}
    (hm : Measurable f) (hc : ContinuousOn f (Ici a)) (hn : ∀ s, a ≤ s → 0 ≤ f s)
    {C T : ℝ} (hT : a ≤ T) (hb : ∀ s, T ≤ s → f s ≤ C * Real.exp (-s)) :
    IntegrableOn f (Ici a) := by
  have hcompact : IntegrableOn f (Icc a T) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  have htail : IntegrableOn f (Ioi T) := by
    apply ((integrableOn_exp_neg_Ioi T).const_mul C).mono_nonneg hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hn s (hT.trans hs.le)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hb s hs.le
  rw [← Icc_union_Ioi_eq_Ici hT]
  exact hcompact.union htail

theorem weights_exp_majorant : ∃ D U : ℝ, 0 < D ∧ 2 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    phiEven s ≤ D * Real.exp (-s) ∧ phiOdd s ≤ D * Real.exp (-s) := by
  obtain ⟨c, C, hc, hC, hphi⟩ := WeightDickmanComparison.weights_dickman_bounds
  obtain ⟨R, hR, T, hT, hrho⟩ := DickmanDecay.rho_exponential_majorant 1
  refine ⟨C * R * Real.exp 2, T + 2, by positivity, by linarith, ?_⟩
  intro s hs
  have hs2 : 2 ≤ s := by linarith
  have hr := hrho (s - 2) (by linarith)
  have heq : Real.exp (-(s - 2)) = Real.exp 2 * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_one_mul, heq] at hr
  have hbound : C * Dickman.rho (s - 2) ≤ (C * R * Real.exp 2) * Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hr hC.le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact ⟨(hphi s hs2).1.2.trans hbound, (hphi s hs2).2.2.trans hbound⟩

theorem phiEven_integrableOn : IntegrableOn phiEven (Ici (2 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  apply integrableOn_Ici_of_exp_tail phiEven_measurable ?_
    (fun s hs ↦ (phiEven_pos (by linarith)).le) hU (fun s hs ↦ (hb s hs).1)
  intro s hs
  exact (phiEven_continuousAt (by change (2 : ℝ) ≤ s at hs; linarith)).continuousWithinAt

theorem phiOdd_integrableOn : IntegrableOn phiOdd (Ici (1 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  exact integrableOn_Ici_of_exp_tail phiOdd_continuous.measurable phiOdd_continuous.continuousOn
    (fun s _ ↦ (phiOdd_pos s).le) (show (1 : ℝ) ≤ U by linarith) (fun s hs ↦ (hb s hs).2)

theorem evenDensity_integrable : Integrable InvariantDensities.evenDensity :=
  (integrable_indicator_iff measurableSet_Ici).mpr phiEven_integrableOn

theorem oddDensity_integrable : Integrable InvariantDensities.oddDensity := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply phiOdd_integrableOn.mono_nonneg
    (oddFactor_measurable.mul phiOdd_continuous.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have h := mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul]

instance evenMeasure_isFiniteMeasure : IsFiniteMeasure evenMeasure := by
  constructor
  rw [evenMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal evenDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.evenDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

instance oddMeasure_isFiniteMeasure : IsFiniteMeasure oddMeasure := by
  constructor
  rw [oddMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal oddDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

end Erdos970Dependency.InvariantFiniteness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StateKernelInvariance
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateKernelInvariance
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.OrdinaryKernelInvariance

instance evenStateMeasure_isFiniteMeasure : IsFiniteMeasure evenStateMeasure := by unfold evenStateMeasure; infer_instance
instance oddStateMeasure_isFiniteMeasure : IsFiniteMeasure oddStateMeasure := by unfold oddStateMeasure; infer_instance

instance stateMeasure_isFiniteMeasure : IsFiniteMeasure stateMeasure := by unfold stateMeasure; infer_instance

end Erdos970Dependency.StateKernelInvariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.AdmissibleCycleTests

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation CycleResponse

theorem HasCompactBound.mask {F : Test} (hF : HasCompactBound F) (B : Set (ℝ × State)) :
    HasCompactBound (mask B F) := by
  classical
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨C, M, hC, hM, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · simpa [AdmissibleCycleTests.mask, hx] using hb x
    · simpa [AdmissibleCycleTests.mask, hx] using hC
  · intro x hx
    by_cases h : x ∈ B <;> simp [AdmissibleCycleTests.mask, h, hs x hx]

theorem HasCompactBound.add {F G : Test} (hF : HasCompactBound F) (hG : HasCompactBound G) :
    HasCompactBound (fun x => F x + G x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  obtain ⟨D, N, hD, hN, hb', hs'⟩ := hG
  refine ⟨C + D, max M N, add_nonneg hC hD, le_trans hM (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact le_trans (norm_add_le _ _) (add_le_add (hb x) (hb' x))
  · intro x hx
    change F x + G x = 0
    rw [hs x (lt_of_le_of_lt (le_max_left _ _) hx), hs' x (lt_of_le_of_lt (le_max_right _ _) hx), add_zero]

theorem HasCompactBound.scale {F : Test} (hF : HasCompactBound F) (c : ℝ) :
    HasCompactBound (fun x => c * F x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨‖c‖ * C, M, mul_nonneg (norm_nonneg _) hC, hM, ?_, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  · intro x hx
    change c * F x = 0
    rw [hs x hx, mul_zero]

theorem Admissible.measurable {F : Test} (hF : Admissible F) : Measurable F := by
  induction hF with
  | base hf _ _ => exact hf
  | upper _ a ih => exact ih.indicator (measurableSet_le measurable_fst measurable_const)
  | upperOpen _ a ih => exact ih.indicator (measurableSet_lt measurable_fst measurable_const)
  | state _ B hB ih => exact ih.indicator (measurable_snd hB)
  | arrival _ ell _ ih =>
    exact ih.indicator (measurableSet_lt (stateRatio_measurable.comp measurable_snd)
      ((Real.measurable_exp.comp measurable_fst).div_const ell))
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact measurable_const.mul ih

theorem Admissible.compactBound {F : Test} (hF : Admissible F) : HasCompactBound F := by
  induction hF with
  | base _ _ hb => exact hb
  | upper _ _ ih => exact ih.mask _
  | upperOpen _ _ ih => exact ih.mask _
  | state _ _ _ ih => exact ih.mask _
  | arrival _ _ _ ih => exact ih.mask _
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact ih.scale c

end NumberTheoryLean.AdmissibleCycleTests



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DeficitIntegralValues
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.DeficitIntegralValues
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals

theorem shift_indicator (f : ℝ → ℝ) (a d : ℝ) :
    (fun s ↦ (Ioi a).indicator f (s - d)) = (Ioi (a + d)).indicator (fun s ↦ f (s - d)) := by
  funext s
  by_cases hs : a + d < s
  · rw [indicator_of_mem (show s ∈ Ioi (a + d) from hs),
      indicator_of_mem (show s - d ∈ Ioi a by change a < s - d; linarith)]
  · rw [indicator_of_notMem (show s ∉ Ioi (a + d) from hs),
      indicator_of_notMem (show s - d ∉ Ioi a by change ¬a < s - d; linarith)]

theorem integrableOn_shift_Ioi {f : ℝ → ℝ} {a : ℝ} (hf : IntegrableOn f (Ioi a)) (d : ℝ) :
    IntegrableOn (fun s ↦ f (s - d)) (Ioi (a + d)) := by
  have h := ((integrable_indicator_iff measurableSet_Ioi).mpr hf).comp_sub_right d
  rw [shift_indicator] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

theorem integral_shift_Ioi (f : ℝ → ℝ) (a d : ℝ) :
    (∫ s in Ioi (a + d), f (s - d)) = ∫ s in Ioi a, f s := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) ((Ioi a).indicator f) d
  rw [shift_indicator, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

theorem upper_integral_one : IntegrableOn upperDeficit (Ioi (1 : ℝ)) ∧
    (∫ s in Ioi (1 : ℝ), upperDeficit s) = 2 := by
  have h := lower_future_integral (s := 2) (by norm_num)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  norm_num [lowerDeficit, f_initial sieveA (s := 2) (by norm_num)]

theorem lower_integral_two : IntegrableOn lowerDeficit (Ioi (2 : ℝ)) ∧
    (∫ s in Ioi (2 : ℝ), lowerDeficit s) = sieveA - 3 := by
  have h := upper_future_integral (s := 3) (by norm_num)
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  simp only [upperDeficit, F_initial sieveA (s := 3) (by norm_num) (by norm_num)]
  ring

theorem even_majorant_integral :
    IntegrableOn (fun s ↦ lowerDeficit s + upperDeficit (s - 1)) (Ici (2 : ℝ)) ∧
      (∫ s in Ici (2 : ℝ), lowerDeficit s + upperDeficit (s - 1)) = sieveA - 1 := by
  have ha := lower_integral_two.1
  have hc : IntegrableOn (fun s ↦ upperDeficit (s - 1)) (Ioi (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using integrableOn_shift_Ioi upper_integral_one.1 1
  refine ⟨Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (ha.add hc), ?_⟩
  rw [integral_Ici_eq_integral_Ioi, integral_add ha hc, lower_integral_two.2]
  have h := integral_shift_Ioi upperDeficit 1 1
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at h
  rw [h, upper_integral_one.2]
  ring

end Erdos970Dependency.DeficitIntegralValues

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OnePairCost
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities Erdos970Dependency.DeficitIntegralValues

theorem cost_le_inv {s : ℝ} (hs : 0 < s) : cost s ≤ 1 / s := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / s by positivity)
  change Real.log (1 + 1 / s) ≤ 1 / s
  linarith

theorem evenCost_nonneg (s : ℝ) : 0 ≤ evenCost s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact mul_nonneg (phiEven_pos (by linarith)).le (cost_pos (by linarith)).le
  · rw [evenCost, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_nonneg (s : ℝ) : 0 ≤ oddCost s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost]
    exact mul_nonneg (oddDensity_nonneg s) (cost_pos (by linarith)).le
  · rw [oddCost, oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenCost_le_major (s : ℝ) : evenCost s ≤ evenMajor s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    calc
      phiEven s * cost s ≤ phiEven s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiEven_pos (by linarith)).le
      _ = _ := by rw [phiEven_eq_deficits hs]; field_simp
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem evenMajor_integrable : Integrable evenMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr even_majorant_integral.1

theorem evenCost_integrable : Integrable evenCost := by
  apply evenMajor_integrable.mono' (evenDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖evenCost s‖ ≤ evenMajor s
    rw [Real.norm_of_nonneg (evenCost_nonneg s)]
    exact evenCost_le_major s)

theorem even_cost_pos : 0 < ∫ s, evenCost s := by
  apply (integral_pos_iff_support_of_nonneg evenCost_nonneg evenCost_integrable).mpr
  have hsub : Icc (2 : ℝ) 3 ⊆ Function.support evenCost := by
    intro s hs
    apply ne_of_gt
    rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs.1)]
    exact mul_pos (phiEven_pos (by linarith [hs.1])) (cost_pos (by linarith [hs.1]))
  exact lt_of_lt_of_le (by norm_num [Real.volume_Icc] : 0 < volume (Icc (2 : ℝ) 3)) (measure_mono hsub)

theorem costMass_pos : 0 < costMass :=
  add_pos_of_pos_of_nonneg even_cost_pos (integral_nonneg oddCost_nonneg)

end Erdos970Dependency.InvariantCostBound

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry PrimeHistoryHorizon KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

end NumberTheoryLean.ActualCouplingUpdates

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SuccessfulRewardComparison
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulRewardComparison

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualFlagInvariant DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry

theorem stateWeight_eq (s : State) : stateWeight s = weight (stateSide s) (stateRatio s) := by
  cases s <;> rfl

end NumberTheoryLean.SuccessfulRewardComparison

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

namespace NumberTheoryLean.CompactInverseTest

open _root_.Set
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open DerivativeWeights CompactTestGeometry SignedCompactTransfer InvariantInverseWeights

theorem valid_lower (i : Side) (s : ℝ) : Valid i s ↔ lowerRatio i ≤ s := by cases i <;> rfl

theorem safeWeight_pos (i : Side) (s : ℝ) : 0 < safeWeight i s :=
  weight_pos ((valid_lower _ _).mpr (le_max_left _ _))

theorem safeWeight_eq {i : Side} {s : ℝ} (hs : Valid i s) : safeWeight i s = weight i s := by
  unfold safeWeight
  rw [max_eq_right ((valid_lower _ _).mp hs)]

theorem safeWeight_continuous (i : Side) : Continuous (safeWeight i) := by
  cases i with
  | even =>
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : 1 < max (198/100:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact (phiEven_continuousAt hx).comp (continuous_const.max continuous_id).continuousAt
  | odd => exact phiOdd_continuous.comp (continuous_const.max continuous_id)

theorem inverseTest_continuous {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (i : Side) :
    Continuous (inverseTest H i) :=
  ((continuous_fst.pow 2).mul (hH i)).div ((safeWeight_continuous i).comp continuous_snd)
    (fun x => (safeWeight_pos i x.2).ne')

theorem inverseTest_compact {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,HasCompactSupport (H i)) (i : Side) :
    HasCompactSupport (inverseTest H i) := by
  have he : inverseTest H i = (fun x : ℝ×ℝ => x.1^2/safeWeight i x.2)*(H i) := by
    funext x
    dsimp [inverseTest]
    ring
  rw [he]
  exact (hH i).mul_left

theorem inverseTest_bounded {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|inverseTest H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (inverseTest_continuous hH .even).bounded_above_of_compact_support (inverseTest_compact hcompact .even)
  obtain ⟨Ao,ho⟩ := (inverseTest_continuous hH .odd).bounded_above_of_compact_support (inverseTest_compact hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |inverseTest H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |inverseTest H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem inverseTest_eq {H : Side → ℝ×ℝ → ℝ} {i : Side} {r s : ℝ} (hs : Valid i s) :
    inverseTest H i (r,s) = r^2*H i (r,s)/weight i s := by
  simp only [inverseTest,safeWeight_eq hs]

end NumberTheoryLean.CompactInverseTest

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RetainedOccupationLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactLogOccupationTest

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactTestGeometry ActualCouplingUpdates
open CycleResponse AdmissibleCycleTests ArrivalKernelGeometry RegeneratingInverseBands
open NormalizedOccupationLimit EvenStartOccupation

theorem logTest_measurable {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) : Measurable (logTest H) := by
  have hcoord : Measurable (fun x : ℝ×State => (Real.exp x.1,stateRatio x.2)) :=
    (Real.measurable_exp.comp measurable_fst).prodMk (stateRatio_measurable.comp measurable_snd)
  have hside : MeasurableSet {x : ℝ×State | stateSide x.2 = .even} :=
    measurable_snd (side_set_measurable .even)
  have heq : logTest H = (fun x => if stateSide x.2 = .even then inverseTest H .even (Real.exp x.1,stateRatio x.2)
      else inverseTest H .odd (Real.exp x.1,stateRatio x.2)) := by
    funext x
    rcases x with ⟨u,s⟩
    cases s <;> rfl
  rw [heq]
  exact Measurable.ite hside ((inverseTest_continuous hH .even).measurable.comp hcoord)
    ((inverseTest_continuous hH .odd).measurable.comp hcoord)

theorem logTest_continuous_shift {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (s : State) :
    Continuous (fun u => logTest H (u,s)) := by
  change Continuous (fun u : ℝ => inverseTest H (stateSide s) (Real.exp u,stateRatio s))
  exact (inverseTest_continuous hH (stateSide s)).comp (Real.continuous_exp.prodMk continuous_const)

theorem logTest_compact_bound {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : HasCompactBound (logTest H) := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  refine ⟨A,M,hA,hM,?_,?_⟩
  · intro x
    simpa only [logTest,Real.norm_eq_abs] using hbound (stateSide x.2) (Real.exp x.1,stateRatio x.2)
  · rintro ⟨u,s⟩ hu
    have hcase : u < Real.log a ∨ Real.log b < u := by
      by_contra hn
      push Not at hn
      have hlo := neg_abs_le (Real.log a)
      have hup := le_abs_self (Real.log b)
      have hle : |u| ≤ M := abs_le.mpr ⟨by dsimp [M] <;> linarith [abs_nonneg (Real.log b)],by dsimp [M] <;> linarith [abs_nonneg (Real.log a)]⟩
      exact (not_lt_of_ge hle) hu
    have hzero : H (stateSide s) (Real.exp u,stateRatio s) = 0 := by
      apply hsupport
      rcases hcase with h | h
      · exact Or.inl (by simpa only [Real.exp_log ha] using Real.exp_lt_exp.mpr h)
      · exact Or.inr (by simpa only [Real.exp_log hb] using Real.exp_lt_exp.mpr h)
    simp [logTest,inverseTest,hzero]

theorem logTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (logTest H) :=
  Admissible.base (logTest_measurable hH) (logTest_continuous_shift hH)
    (logTest_compact_bound hH hcompact ha hb hsupport)

theorem arrivalTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (arrivalTest ell H) :=
  (logTest_admissible hH hcompact ha hb hsupport).arrival ell hell

end NumberTheoryLean.CompactLogOccupationTest

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

theorem literal_original_prime_occupation {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/FinitePathGeometry.weight start.side start.ratio)*
          (∑ ps ∈ ActualPrimeHigh.uncappedPrefixes w ell start,
            ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps*
              H (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio))-
          invariantAverage (arrivalTest ell H)| ≤ ε := by
  simpa only [uncappedFamilyValue,nodeReward] using
    original_prime_continuous_occupation_limit hH hcompact ha hb hell hsupport d ε hd hε

end NumberTheoryLean.OriginalPrimeOccupationLimit

end

section

namespace NumberTheoryLean.PrimeOccupationDensity

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

theorem density_nonneg (ell : ℝ) (x : ℝ×State) : 0 ≤ density ell x := by
  unfold density
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_pos (stateWeight_pos _) costMass_pos).le
  · exact le_rfl

theorem density_measurable (ell : ℝ) : Measurable (density ell) := by
  have he := Real.measurable_exp.comp (measurable_fst : Measurable (Prod.fst : ℝ×State → ℝ))
  have hs := stateRatio_measurable.comp (measurable_snd : Measurable (Prod.snd : ℝ×State → State))
  exact Measurable.ite (measurableSet_lt hs (he.div_const ell))
    ((he.pow_const 2).div ((stateWeight_measurable.comp measurable_snd).mul_const costMass)) measurable_const

end NumberTheoryLean.PrimeOccupationDensity

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

end NumberTheoryLean.UncappedCompactMass

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceSourceDecomposition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBoundaryDomain

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ActualPrimeHigh SourceNodeCoordinates
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem child_boundary_domain {w ell : ℝ} {z : Node} {p : ℕ} (hell : 2 ≤ ell)
    (heven : z.side=.even → 2 ≤ z.ratio) (hp : p ∈ uncappedChildren w ell z) :
    BoundaryDomain (step w z p).side (step w z p).gap ∧
      ((step w z p).side=.even → 2 ≤ (step w z p).ratio) := by
  obtain ⟨_hprime,hlo,_hcap,hmin⟩ := Finset.mem_filter.mp hp
  have hx : 2 < primeExponent w p := hell.trans_lt hlo
  have he : (step w z p).ratio*primeExponent w p=(step w z p).gap := by
    dsimp only [step,childRatio]
    field_simp [show primeExponent w p ≠ 0 by linarith]
  cases hi : z.side with
  | even =>
    have hs := heven hi
    have hm : 1 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      change z.ratio-1 ≤ (step w z p).ratio at hmin
      linarith
    have hside : (step w z p).side=.odd := by simp [step,hi,Side.flip]
    rw [hside]
    refine ⟨?_,by intro h; cases h⟩
    change 2 ≤ (step w z p).gap
    nlinarith
  | odd =>
    have hm : 2 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      exact (le_max_left _ _).trans hmin
    have hside : (step w z p).side=.even := by simp [step,hi,Side.flip]
    rw [hside]
    exact ⟨by change 4 ≤ (step w z p).gap; nlinarith,fun _ => hm⟩

theorem boundary_domain_preserved {w ell : ℝ} {z : Node} {ps : List ℕ} (hell : 2 ≤ ell)
    (hdom : BoundaryDomain z.side z.gap) (heven : z.side=.even → 2 ≤ z.ratio)
    (hp : uncappedAllowed w ell z ps) :
    BoundaryDomain (terminal w z ps).side (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact hdom
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    obtain ⟨hd,he⟩ := child_boundary_domain hell heven hc
    exact ih hd he ht

theorem source_boundary_domain {B w ell : ℝ} (hB : 4 ≤ B) (hell : 2 ≤ ell)
    (start : Node) (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff=B) {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps) :
    BoundaryDomain (terminal w start ps).side (terminal w start ps).gap := by
  obtain ⟨hs,_hr,hBgap,_hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hc hcut
  have hgap := node_gap_eq hs hc hcut
  cases ps with
  | nil => simpa only [terminal_nil,hi,BoundaryDomain] using hB.trans hBgap
  | cons p ps =>
    obtain ⟨hchild,htail⟩ := hp
    obtain ⟨_hprime,_hlo,hcap,_hmin⟩ := Finset.mem_filter.mp hchild
    have hxp : primeExponent w p ≤ B := by
      change capGuard start.closed start.cutoff (primeExponent w p) at hcap
      rw [hcut] at hcap
      cases hcl : start.closed with
      | false =>
        have h : primeExponent w p < B := by simpa [capGuard,hcl] using hcap
        exact h.le
      | true => simpa only [capGuard,hcl,ite_true, if_true] using hcap
    have hside : (step w start p).side=.odd := by simp [step,hi,Side.flip]
    have hdom : BoundaryDomain (step w start p).side (step w start p).gap := by
      rw [hside]
      change 2 ≤ start.gap-primeExponent w p
      nlinarith
    simpa only [terminal_cons] using boundary_domain_preserved (z := step w start p) hell hdom (by rw [hside]; intro h; cases h) htail

theorem boundary_gap_ge_two {i : Side} {r : ℝ} (h : BoundaryDomain i r) : 2 ≤ r := by
  cases i <;> simp only [BoundaryDomain] at h <;> linarith

end NumberTheoryLean.ActualBoundaryDomain

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CompactAnomalyTest
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass

theorem terminal_side_sign (w : ℝ) (z : Node) (ps : List ℕ) :
    sideSign (terminal w z ps).side=sideSign z.side*(-1:ℝ)^ps.length := by
  induction ps generalizing z with
  | nil => simp only [terminal_nil,List.length_nil,pow_zero,mul_one]
  | cons p ps ih =>
    rw [terminal_cons,ih,List.length_cons,pow_succ]
    have he : sideSign (step w z p).side = -sideSign z.side := by
      cases h : z.side <;> simp [step,h,Side.flip,sideSign]
    rw [he]
    ring

theorem source_parity_sign (w : ℝ) (z : Node) (hz : z.side=.even) (ps : List ℕ) :
    (-1:ℝ)^ps.length=sideSign (terminal w z ps).side := by
  rw [terminal_side_sign,hz,sideSign,one_mul]

theorem continuousBoundaryCorrection_eq_state_reward (w ell : ℝ) (start : Node)
    (hi : start.side=.even) :
    continuousBoundaryCorrection w ell start=
      ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
        signedAnomaly (terminal w start ps).side (terminal w start ps).gap := by
  unfold continuousBoundaryCorrection signedAnomaly
  apply Finset.sum_congr rfl
  intro ps _
  rw [source_parity_sign w start hi ps]

end ErdosContinuousAnomaly

end

section

open _root_.Set
namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PositiveGapMajorant

theorem extendedSignedAnomaly_continuous (i : Side) : Continuous (extendedSignedAnomaly i) := by
  have h := (continuousAnomaly_continuousOn i).comp_continuous
    (continuous_const.max continuous_id) (fun r => le_max_left 2 r)
  exact continuous_const.mul h

theorem extendedSignedAnomaly_eq (i : Side) {r : ℝ} (hr : 2 ≤ r) :
    extendedSignedAnomaly i r=signedAnomaly i r := by
  simp only [extendedSignedAnomaly,signedAnomaly,max_eq_right hr]

theorem compactCutoff_spec (K : ℝ) :
    HasCompactSupport (compactCutoff K) ∧ (∀ x,0 ≤ compactCutoff K x ∧ compactCutoff K x ≤ 1) ∧
    (∀ r s,2 ≤ r → r ≤ K → 0 ≤ s → s ≤ K → compactCutoff K (r,s)=1) ∧
    ∀ r s,r < 1 ∨ K+1 < r → compactCutoff K (r,s)=0 :=
  Classical.choose_spec (exists_positive_gap_majorant K)

theorem compactAnomalyTest_continuous (K : ℝ) (i : Side) : Continuous (compactAnomalyTest K i) :=
  (compactCutoff K).continuous.mul ((extendedSignedAnomaly_continuous i).comp continuous_fst)

theorem compactAnomalyTest_compact (K : ℝ) (i : Side) : HasCompactSupport (compactAnomalyTest K i) := by
  exact (compactCutoff_spec K).1.mul_right

theorem compactAnomalyTest_support (K : ℝ) (i : Side) (r s : ℝ)
    (hr : r < 1 ∨ K+1 < r) : compactAnomalyTest K i (r,s)=0 := by
  unfold compactAnomalyTest
  rw [(compactCutoff_spec K).2.2.2 r s hr,zero_mul]

theorem compactAnomalyTest_eq (K : ℝ) (i : Side) {r s : ℝ}
    (hr : 2 ≤ r) (hrK : r ≤ K) (hs : 0 ≤ s) (hsr : s ≤ r) :
    compactAnomalyTest K i (r,s)=signedAnomaly i r := by
  unfold compactAnomalyTest
  rw [(compactCutoff_spec K).2.2.1 r s hr hrK hs (hsr.trans hrK),one_mul,extendedSignedAnomaly_eq i hr]

theorem compactAnomalyTest_error (K : ℝ) (i : Side) {r s : ℝ}
    (hr : 2 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) :
    |signedAnomaly i r-compactAnomalyTest K i (r,s)| ≤
      if K < r then |continuousAnomaly i r| else 0 := by
  by_cases hrK : r ≤ K
  · rw [compactAnomalyTest_eq K i hr hrK hs hsr,sub_self,abs_zero,ite_eq_right (not_lt_of_ge hrK)]
  · rw [ite_eq_left (lt_of_not_ge hrK)]
    have hb := (compactCutoff_spec K).2.1 (r,s)
    have he : signedAnomaly i r-compactAnomalyTest K i (r,s)=
        (1-compactCutoff K (r,s))*(sideSign i*continuousAnomaly i r) := by
      simp only [compactAnomalyTest,extendedSignedAnomaly_eq i hr,signedAnomaly]
      ring
    rw [he,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-compactCutoff K (r,s)),abs_mul]
    have hsign : |sideSign i|=1 := by cases i <;> norm_num [sideSign]
    rw [hsign,one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CompactCorrectionLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosCorrectionOccupation
attribute [local instance] Classical.propDecidable
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.UncappedCompactMass NumberTheoryLean.SourceNodeCoordinates
open NumberTheoryLean.ActualBoundaryDomain NumberTheoryLean.LiteralUniformPrimeTail
open NumberTheoryLean.LiteralPrimeOccupation
open ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail

theorem compact_correction_error {C c K B w ell : ℝ}
    (hA : ∀ r : ℝ,2 ≤ r → ∀ i : Side,|continuousAnomaly i r| ≤ C*Real.exp (-c*r))
    (hB : 4 ≤ B) (hell : 2 ≤ ell) (hellB : ell ≤ B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    |continuousBoundaryCorrection w ell start-compactCorrection K w ell start| ≤
      C*(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*tailListReward c K w start ps) := by
  obtain ⟨hs,hr,_hBgap,_hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hcons hcut
  rw [continuousBoundaryCorrection_eq_state_reward w ell start hi,compactCorrection,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ps hp
  have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
  have hr2 := boundary_gap_ge_two (source_boundary_domain hB hell start hi h199 h23 hcons hcut hpA)
  have hratio := uncapped_terminal_ratio_le_gap (by linarith : 1 ≤ ell) hr hs hcons (by rwa [hcut]) hpA
  have he := compactAnomalyTest_error K (terminal w start ps).side hr2 hratio.1.le hratio.2
  have henv : (if K < (terminal w start ps).gap then |continuousAnomaly (terminal w start ps).side (terminal w start ps).gap| else 0) ≤
      C*tailListReward c K w start ps := by
    unfold tailListReward
    split_ifs
    · exact hA _ hr2 _
    · simp
  rw [← mul_sub,abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
  have hh := mul_le_mul_of_nonneg_left (he.trans henv) (prefixWeight_nonneg ps)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ErdosCorrectionOccupation

end

section

namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.OriginalPrimeOccupationLimit
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit

theorem fixed_compact_correction_limit (K ell d eps : ℝ) (hK : 3 ≤ K) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/weight start.side start.ratio)*compactCorrection K w ell start-
          invariantAverage (arrivalTest ell (compactAnomalyTest K))| ≤ eps := by
  simpa only [compactCorrection] using
    literal_original_prime_occupation
      (fun i => compactAnomalyTest_continuous K i)
      (fun i => compactAnomalyTest_compact K i)
      (by norm_num : (0:ℝ)<1) (by linarith : 0<K+1) (by linarith : 1≤ell)
      (fun i r s hr => compactAnomalyTest_support K i r s hr) d eps hd heps

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationDensityIntegral
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OccupationDensityIntegral

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open CompactInverseTest CompactLogOccupationTest PrimeOccupationDensity
open CycleResponse AdmissibleCycleTests NormalizedOccupationLimit OccupationConstant
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

theorem density_mul_raw (ell : ℝ) (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) :
    density ell x*rawTest H x = arrivalTest ell H x/costMass := by
  classical
  by_cases h : stateRatio x.2 < Real.exp x.1/ell
  · change (if stateRatio x.2 < Real.exp x.1/ell then (Real.exp x.1)^2/(stateWeight x.2*costMass) else 0)*rawTest H x =
      (if stateRatio x.2 < Real.exp x.1/ell then logTest H x else 0)/costMass
    rw [ite_eq_left h,ite_eq_left h]
    unfold logTest
    rw [inverseTest_eq (stateRatio_valid x.2),← SuccessfulRewardComparison.stateWeight_eq]
    unfold rawTest
    ring
  · simp [density,arrivalTest,AdmissibleCycleTests.mask,h]

theorem compactBound_product_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    Integrable F baseMeasure := by
  obtain ⟨C,M,hC,hM,hbound,hsupport⟩ := hB
  let A : Set (ℝ×State) := Icc (-M) M ×ˢ univ
  have hA : MeasurableSet A := measurableSet_Icc.prod MeasurableSet.univ
  have hfin : baseMeasure A < ∞ := by
    rw [baseMeasure,Measure.prod_prod,Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top stateMeasure univ)
  let : IsFiniteMeasure (baseMeasure.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hdom : Integrable (A.indicator (fun _ => C)) baseMeasure :=
    (integrable_indicator_iff hA).mpr (integrable_const C)
  apply hdom.mono' hF.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    exact hbound x
  · have hlarge : M < |x.1| := by
      apply lt_of_not_ge
      intro hh
      exact hx ⟨abs_le.mp hh,Set.mem_univ _⟩
    rw [hsupport x hlarge, norm_zero,indicator_of_notMem hx]

theorem rawTest_integrable {H : Side → ℝ×ℝ → ℝ} (ell : ℝ)
    (hF : Measurable (arrivalTest ell H)) (hB : HasCompactBound (arrivalTest ell H)) :
    Integrable (rawTest H) (limitingMeasure ell) := by
  have hI := compactBound_product_integrable hF hB
  have hD : Measurable (fun x => ENNReal.ofReal (density ell x)) := ENNReal.measurable_ofReal.comp (density_measurable ell)
  have htop : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density ell x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' hD htop).mpr
  have he : (fun x => (ENNReal.ofReal (density ell x)).toReal • rawTest H x) =
      (fun x => arrivalTest ell H x/costMass) := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg ell x),smul_eq_mul,density_mul_raw]
  rw [he]
  exact hI.div_const costMass

theorem limiting_integral_eq_invariant {H : Side → ℝ×ℝ → ℝ} (ell : ℝ)
    (hF : Measurable (arrivalTest ell H)) (hB : HasCompactBound (arrivalTest ell H)) :
    (∫ x,rawTest H x ∂limitingMeasure ell) = invariantAverage (arrivalTest ell H) := by
  have hI := compactBound_product_integrable hF hB
  have hD : Measurable (fun x => ENNReal.ofReal (density ell x)) := ENNReal.measurable_ofReal.comp (density_measurable ell)
  have htop : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density ell x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [limitingMeasure,integral_withDensity_eq_integral_toReal_smul hD htop]
  have he : (fun x => (ENNReal.ofReal (density ell x)).toReal • rawTest H x) =
      (fun x => arrivalTest ell H x/costMass) := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg ell x),smul_eq_mul,density_mul_raw]
  rw [he,integral_div]
  have hfubini := integral_prod_symm (arrivalTest ell H) hI
  change (∫ x,arrivalTest ell H x ∂baseMeasure)/costMass = _
  rw [baseMeasure,hfubini]
  rfl

theorem continuous_test_density {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    Integrable (rawTest H) (limitingMeasure ell) ∧
      (∫ x,rawTest H x ∂limitingMeasure ell) = invariantAverage (arrivalTest ell H) := by
  have htest := arrivalTest_admissible hH hcompact ha hb hell hsupport
  exact ⟨rawTest_integrable ell htest.measurable htest.compactBound,
    limiting_integral_eq_invariant ell htest.measurable htest.compactBound⟩

end NumberTheoryLean.OccupationDensityIntegral

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectionWeightedIntegral
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit
open NumberTheoryLean.TransitionKernels
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness

theorem compact_invariant_tendsto :
    Tendsto (fun K : ℝ => invariantAverage (arrivalTest 2 (compactAnomalyTest K))) atTop
      (𝓝 (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)) := by
  apply compact_limiting_integral_tendsto_jb247.congr'
  filter_upwards [eventually_ge_atTop (3:ℝ)] with K hK
  exact (continuous_test_density (compactAnomalyTest_continuous K) (compactAnomalyTest_compact K)
    (a := 1) (b := K+1) (by norm_num) (by linarith) (by norm_num : (0:ℝ)<2)
    (fun i r s hr => compactAnomalyTest_support K i r s hr)).2

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionUniformTruncation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.LiteralUniformPrimeTail

theorem uniform_compact_correction_above (Kmin ell d eps : ℝ) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ K B₀ w₀ : ℝ,3 ≤ K ∧ Kmin ≤ K ∧ 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|continuousBoundaryCorrection w ell start-compactCorrection K w ell start| ≤ eps := by
  obtain ⟨C,c,_wA,hC,hc,_hwA,_hD,hA⟩ := common_anomaly_exponential_jb247
  obtain ⟨M₀,BT,wT,hBT,hwT,hT⟩ := actual_uniform_original_prime_tail d c (eps/C) hd hc (div_pos heps hC)
  obtain ⟨n,hn⟩ := exists_nat_ge Kmin
  let M : ℕ := M₀+n
  let K : ℝ := 3*((M:ℝ)+1)
  have hK : 3 ≤ K := by dsimp [K]; have hn := Nat.cast_nonneg (α := ℝ) M; linarith
  have hKmin : Kmin ≤ K := by
    apply hn.trans
    dsimp [K,M]
    push_cast
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    have hm0 := Nat.cast_nonneg (α := ℝ) M₀
    linarith
  refine ⟨K,max BT (max 4 ell),wT,hK,hKmin,hBT.trans_le (le_max_left _ _),hwT,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBT' : BT ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hellB : ell ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have ht := hT M (by dsimp [M]; omega) B w hBT' hw ell (by linarith) hellB hcomp start hi h199 h23 hcons hcut
  have he := compact_correction_error (K := K) (w := w) hA hB4 hell hellB start hi h199 h23 hcons hcut
  have heB := mul_le_mul_of_nonneg_left he (sq_nonneg B)
  have htC := mul_le_mul_of_nonneg_left ht hC.le
  have hcanc : C*(eps/C)=eps := mul_div_cancel₀ eps (ne_of_gt hC)
  rw [hcanc] at htC
  nlinarith

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousCorrectionLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit
open NumberTheoryLean.PrimeBinMembership
open NumberTheoryLean.SourceNodeCoordinates NumberTheoryLean.SourceLowRemoval
open Erdos970Dependency.InvariantCostBound

theorem compact_invariant_coefficient_tendsto :
    Tendsto (fun K : ℝ => invariantAverage (arrivalTest 2 (compactAnomalyTest K))) atTop
      (𝓝 (2*signedCoefficientI/costMass)) := by
  simpa only [full_limiting_integral_eq_jb247] using compact_invariant_tendsto

theorem full_continuous_correction_limit (d eps : ℝ) (hd : 0 < d) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/weight start.side start.ratio)*continuousBoundaryCorrection w 2 start-
          2*signedCoefficientI/costMass| ≤ eps := by
  have he3 : 0 < eps/3 := by linarith
  obtain ⟨Kmin,hKmin⟩ := eventually_atTop.mp
    (compact_invariant_coefficient_tendsto.eventually
      (Metric.ball_mem_nhds (2*signedCoefficientI/costMass) he3))
  obtain ⟨K,BT,wT,hK,hKK,hBT,hwT,hT⟩ :=
    uniform_compact_correction_above Kmin 2 d (eps/(3*scaleConstant))
      le_rfl hd (div_pos heps (mul_pos (by norm_num) scaleConstant_pos))
  obtain ⟨BF,wF,hBF,hwF,hF⟩ := fixed_compact_correction_limit K 2 d (eps/3) hK le_rfl hd he3
  refine ⟨max BT BF,max wT wF,hBT.trans_le (le_max_left _ _),hwT.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBT' : BT ≤ B := (le_max_left _ _).trans hB
  have hBF' : BF ≤ B := (le_max_right _ _).trans hB
  have hwT' : wT ≤ w := (le_max_left _ _).trans hw
  have hwF' : wF ≤ w := (le_max_right _ _).trans hw
  have hBpos : 0 < B := hBT.trans_le hBT'
  have ht := hT B w hBT' hwT' hcomp start hi h199 h23 hcons hcut
  have hf := hF B w hBF' hwF' hcomp start hi h199 h23 hcons hcut
  have hk : |invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass| < eps/3 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hKmin K hKK
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hn : 0 ≤ start.gap^2/weight start.side start.ratio := div_nonneg (sq_nonneg _) (weight_pos hs).le
  have hscale := node_scale_upper hBpos start hi h199 h23 hcons hcut
  have herr : |(start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start)| ≤ eps/3 := by
    rw [abs_mul,abs_of_nonneg hn]
    have hh := mul_le_mul_of_nonneg_right hscale
      (abs_nonneg (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))
    have ht' := mul_le_mul_of_nonneg_left ht scaleConstant_pos.le
    have hcancel : scaleConstant*(eps/(3*scaleConstant))=eps/3 := by
      field_simp [scaleConstant_pos.ne']
    rw [hcancel] at ht'
    nlinarith
  have hsum := abs_add_le ((start.gap^2/weight start.side start.ratio)*
    (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))
    ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
      invariantAverage (arrivalTest 2 (compactAnomalyTest K)))
  have hsum' := abs_add_le
    (((start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))+
      ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
        invariantAverage (arrivalTest 2 (compactAnomalyTest K))))
    (invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass)
  have heq : ((start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))+
      ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
        invariantAverage (arrivalTest 2 (compactAnomalyTest K)))+
      (invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass)=
      (start.gap^2/weight start.side start.ratio)*continuousBoundaryCorrection w 2 start-
        2*signedCoefficientI/costMass := by ring
  rw [heq] at hsum'
  linarith

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_JacobsthalSourceScale
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.JacobsthalSourceScale

open _root_.Filter _root_.Asymptotics
open scoped Topology

theorem log_square_le_sqrt_eventually : ∀ᶠ L : ℝ in atTop,(Real.log L)^2 ≤ Real.sqrt L := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1/2) (by norm_num)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with L hL hpos
  have hr : 0 ≤ L^((1/2:ℝ)) := Real.rpow_nonneg (by linarith) _
  simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hr,one_mul,← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg L)] using hL

theorem sourceW_bounds_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ Real.sqrt L ≤ sourceW L ∧ sourceW L ≤ L := by
  filter_upwards [log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hsmall hL hlog
  have hL0 : 0 < L := by linarith
  have hden : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq : Real.sqrt L ≤ sourceW L := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hlow : 1 < Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hL
  refine ⟨hlow.trans_le hsq,hsq,?_⟩
  exact div_le_self hL0.le (by nlinarith : 1 ≤ (Real.log L)^2)

theorem sourceW_tendsto : Tendsto sourceW atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [sourceW_bounds_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L hW hR
  exact hR.trans hW.2.1

theorem source_scale_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ 0 < sourceB L ∧ Real.sqrt L ≤ sourceB L ∧ sourceB L ≤ L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) := by
  filter_upwards [sourceW_bounds_eventually,log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    sourceW_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with L hW hsmall hL hlog hWexp
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < sourceW L := by linarith [hW.1]
  have hlogW : 1 ≤ Real.log (sourceW L) := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hWexp
  have hlogWL : Real.log (sourceW L) ≤ Real.log L := Real.log_le_log hW0 hW.2.2
  have hlogSmall : Real.log (sourceW L) ≤ Real.sqrt L := by
    have hh : Real.log L ≤ (Real.log L)^2 := by nlinarith
    exact hlogWL.trans (hh.trans hsmall)
  have hBpos : 0 < sourceB L := div_pos hL0 (by linarith)
  have hBsq : Real.sqrt L ≤ sourceB L := by
    apply (le_div_iff₀ (show 0 < Real.log (sourceW L) by linarith)).mpr
    have hm := mul_le_mul_of_nonneg_left hlogSmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hBL : sourceB L ≤ L := div_le_self hL0.le hlogW
  have hLWsq : L ≤ (sourceW L)^2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg L) hW.2.1
    nlinarith [Real.sq_sqrt hL0.le]
  have hcomp := Real.log_le_log hBpos (hBL.trans hLWsq)
  refine ⟨hW.1,hBpos,hBsq,hBL,?_⟩
  simpa only [Real.log_pow,Nat.cast_ofNat] using hcomp

theorem sourceB_tendsto : Tendsto sourceB atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [source_scale_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L h hR
  exact hR.trans h.2.2.1

end NumberTheoryLean.JacobsthalSourceScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionFloorRemainder
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.JacobsthalSourceScale

theorem sourcePrefactor_continuousAt : ContinuousAt sourcePrefactor 2 := by
  exact (phiEven_continuousAt (by norm_num : (1:ℝ)<2)).div (continuousAt_id.pow 2) (by norm_num)

theorem sourcePrefactor_two : sourcePrefactor 2=Real.exp Real.eulerMascheroniConstant := by
  unfold sourcePrefactor
  rw [phiEven_initial (s := 2) le_rfl]
  norm_num [evenInitial,sieveA]
  ring

theorem sourcePrefactor_limit {s : ℝ → ℝ} (hs : Tendsto s atTop (𝓝 2)) :
    Tendsto (fun L => sourcePrefactor (s L)) atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  simpa only [sourcePrefactor_two] using! sourcePrefactor_continuousAt.tendsto.comp hs

theorem paper_ratio_tendsto (a : ℝ) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => paperGap a e L/sourceB L) atTop (𝓝 2) := by
  have hn : Tendsto (fun L : ℝ => (-a+2+e L)/sourceB L) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add he).div_atTop sourceB_tendsto)
  have hl : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have ht : Tendsto (fun L : ℝ => 2+(-a+2+e L)/sourceB L-2*(Real.log L/L)) atTop (𝓝 2) := by
    simpa only [add_zero,mul_zero,sub_zero] using (tendsto_const_nhds.add hn).sub (hl.const_mul 2)
  apply ht.congr'
  filter_upwards [source_scale_eventually,eventually_gt_atTop (0:ℝ)] with L hs hL
  have hw : Real.log (sourceW L) ≠ 0 := (Real.log_pos hs.1).ne'
  unfold paperGap sourceB
  field_simp
  ring

theorem paper_prefactor_tendsto (a : ℝ) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => (sourceB L)^2*phiEven (paperGap a e L/sourceB L)/(paperGap a e L)^2)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have ht := sourcePrefactor_limit (paper_ratio_tendsto a he)
  apply ht.congr'
  filter_upwards [source_scale_eventually] with L hs
  unfold sourcePrefactor
  field_simp

end ErdosCorrectionLimit

end

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale

theorem unroundedY_tendsto : Tendsto unroundedY atTop atTop := by
  simpa only [unroundedY,Real.rpow_two] using! tendsto_exp_mul_div_rpow_atTop 2 2 (by norm_num)

theorem floor_log_error_tendsto :
    Tendsto (fun L => Real.log (⌊unroundedY L⌋₊ : ℝ)-(2*L-2*Real.log L)) atTop (𝓝 0) := by
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp unroundedY_tendsto
  have hh := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hratio
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),unroundedY_tendsto.eventually (eventually_ge_atTop (2:ℝ))] with L hL hY
  have hYpos : 0 < unroundedY L := by linarith
  have hfloor : 0 < (⌊unroundedY L⌋₊ : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (by linarith : 1 ≤ unroundedY L))
  have hL0 : L ≠ 0 := by linarith
  change Real.log ((⌊unroundedY L⌋₊ : ℝ)/unroundedY L)=_
  rw [Real.log_div hfloor.ne' hYpos.ne']
  congr 1
  rw [unroundedY,Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 2 hL0),Real.log_exp,Real.log_pow]
  norm_num

theorem floorRemainder_tendsto : Tendsto floorRemainder atTop (𝓝 0) := by
  exact floor_log_error_tendsto.div_atTop (Real.tendsto_log_atTop.comp sourceW_tendsto)

theorem sourceY_exp (L : ℝ) :
    ErdosInverseBoxHeight.sourceY (Real.exp L)=⌊unroundedY L⌋₊ := by
  unfold ErdosInverseBoxHeight.sourceY unroundedY
  rw [Real.log_exp,pow_two,← Real.exp_add]
  congr 2
  ring_nf

theorem paperGap_floor_eq (a : ℝ) {L : ℝ} (hW : 1 < sourceW L) :
    paperGap a floorRemainder L=
      Real.log (ErdosInverseBoxHeight.sourceY (Real.exp L):ℝ)/Real.log (sourceW L)-a+2 := by
  rw [sourceY_exp]
  have hw0 : Real.log (sourceW L) ≠ 0 := (Real.log_pos hW).ne'
  unfold paperGap floorRemainder sourceB
  field_simp
  ring

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PaperContinuousCorrection
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale
open Erdos970Dependency.InvariantCostBound

theorem paper_start_eventually (a : ℝ) (closed : Bool) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ L : ℝ in atTop,
      0 < sourceB L ∧ 1 < sourceW L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) ∧
      199/100 ≤ (paperStart a e closed L).ratio ∧ (paperStart a e closed L).ratio ≤ 23/10 ∧
      0 < (paperStart a e closed L).gap ∧ Consistent (paperStart a e closed L) := by
  have hr := (paper_ratio_tendsto a he).eventually
    (Ioo_mem_nhds (by norm_num : (199:ℝ)/100 < 2) (by norm_num : (2:ℝ) < 23/10))
  filter_upwards [source_scale_eventually,hr] with L hs hr
  have hB : 0 < sourceB L := hs.2.1
  have hg : 0 < paperGap a e L := by
    have hh := (lt_div_iff₀ hB).mp hr.1
    nlinarith
  refine ⟨hB,hs.1,hs.2.2.2.2,hr.1.le,hr.2.le,hg,?_⟩
  change sourceB L=paperGap a e L/(paperGap a e L/sourceB L)
  field_simp

theorem paper_normalized_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => ((paperStart a e closed L).gap^2/weight .even (paperStart a e closed L).ratio)*
      continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L)) atTop
      (𝓝 (2*signedCoefficientI/costMass)) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := full_continuous_correction_limit 2 (eps/2) (by norm_num) (by linarith)
  filter_upwards [paper_start_eventually a closed he,
    sourceB_tendsto.eventually (eventually_ge_atTop B₀),
    sourceW_tendsto.eventually (eventually_ge_atTop w₀)] with L hs hB hw
  have hh := h (sourceB L) (sourceW L) hB hw hs.2.2.1
    (paperStart a e closed L) rfl hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2 rfl
  rw [Real.dist_eq]
  exact hh.trans_lt (by linarith)

theorem paper_continuous_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => (sourceB L)^2*continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L))
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  have ht := (paper_prefactor_tendsto a he).mul (paper_normalized_correction_tendsto a closed he)
  apply ht.congr'
  filter_upwards [paper_start_eventually a closed he] with L hs
  have hg : paperGap a e L ≠ 0 := hs.2.2.2.2.2.1.ne'
  have hp : phiEven (paperGap a e L/sourceB L) ≠ 0 :=
    (phiEven_pos (by have hh := hs.2.2.2.1; change 199/100 ≤ paperGap a e L/sourceB L at hh; linarith)).ne'
  change (sourceB L)^2*phiEven (paperGap a e L/sourceB L)/(paperGap a e L)^2*
    ((paperGap a e L)^2/phiEven (paperGap a e L/sourceB L)*
      continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L))=_
  field_simp

theorem paper_z_continuous_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun z => (sourceB (Real.log z))^2*
      continuousBoundaryCorrection (sourceW (Real.log z)) 2 (paperStart a e closed (Real.log z))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  exact (paper_continuous_correction_tendsto a closed he).comp Real.tendsto_log_atTop

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCenteredGap
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.PrimeHistories NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale

theorem sourceRoot_eq_paper (a : ℝ) {z : ℝ} (hz : 1 < z) (hW : 1 < sourceW (Real.log z)) :
    sourceRootNode a z=paperStart a floorRemainder true (Real.log z) := by
  have hg := paperGap_floor_eq a (L := Real.log z) hW
  rw [Real.exp_log (by linarith : 0 < z)] at hg
  change paperGap a floorRemainder (Real.log z)=sourceRootGap a z at hg
  unfold sourceRootNode paperStart
  rw [hg]
  rfl

theorem floored_source_correction_tendsto_jb247_oai (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      continuousBoundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  have ht := paper_z_continuous_correction_tendsto a true floorRemainder_tendsto
  apply ht.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hs hz
  rw [sourceRoot_eq_paper a hz hs.1]
  rfl

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247_oai := @OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247_oai
