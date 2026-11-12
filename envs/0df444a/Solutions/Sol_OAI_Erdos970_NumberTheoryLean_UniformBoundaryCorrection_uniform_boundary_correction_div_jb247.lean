-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:09:04.159401+00:00
-- url     : https://prove2.me/submissions/43719fa3-ce2c-49e6-b008-1590606bba33

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
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RetainedOccupationLimit_retained_original_occupation_limit_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_ScaledOriginalTail_actual_uniform_scaled_tail_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_DickmanFiniteDecay
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DickmanFiniteDecay

open Dickman

theorem rho_le_one (u : ℝ) : rho u ≤ 1 := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]
  · have h := rho_antitone (le_of_lt (lt_of_not_ge hu))
    simpa only [rho_initial (le_refl (1:ℝ))] using h

theorem rho_step_power {t u : ℝ} (ht : 1 ≤ t) (htu : t ≤ u) (n : ℕ) :
    t^n*rho (u+(n:ℝ)) ≤ rho u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh := rho_upper_comparison (u := u+(n:ℝ)+1) (by linarith)
    have hs : t*rho (u+(n:ℝ)+1) ≤ rho (u+(n:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right (show t ≤ u+(n:ℝ)+1 by linarith)
        (rho_nonneg (u+(n:ℝ)+1))
      simp only [add_sub_cancel_right] at hh
      exact hm.trans hh
    have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith : 0 ≤ t) n)
    push_cast
    rw [pow_succ]
    simpa only [add_assoc,mul_assoc] using hmul.trans ih

theorem rho_half_power {u : ℝ} (hu : 2 ≤ u) :
    rho u ≤ 1/(u/2)^⌊u/2⌋₊ := by
  have hu0 : 0 < u := by linarith
  have hf := Nat.floor_le (by linarith : 0 ≤ u/2)
  have hh := rho_step_power (t := u/2) (u := u-(⌊u/2⌋₊:ℝ))
    (by linarith) (by linarith) ⌊u/2⌋₊
  simp only [sub_add_cancel] at hh
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < u/2) _)).mpr
  rw [mul_comm]
  exact hh.trans (rho_le_one _)

theorem rho_log_decay {u : ℝ} (hu : 8 ≤ u) :
    rho u ≤ Real.exp (-(1/16:ℝ)*u*Real.log (u+2)) := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < u/2 := by linarith
  have hn : u/4 ≤ (⌊u/2⌋₊:ℝ) := by
    have hf := Nat.lt_floor_add_one (u/2)
    linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hlh : Real.log u/2 ≤ Real.log (u/2) := by
    have hm := Real.log_le_log hu0 (show u ≤ (u/2)^2 by nlinarith)
    rw [Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    linarith
  have hl2 : Real.log (u+2) ≤ 2*Real.log u := by
    have hm := Real.log_le_log (show 0 < u+2 by linarith) (show u+2 ≤ u^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hpow : (1/16:ℝ)*u*Real.log (u+2) ≤ (⌊u/2⌋₊:ℝ)*Real.log (u/2) := by
    have hm := mul_le_mul hn hlh (by linarith : 0 ≤ Real.log u/2) (Nat.cast_nonneg ⌊u/2⌋₊)
    nlinarith [mul_le_mul_of_nonneg_left hl2 hu0.le]
  calc
    _ ≤ 1/(u/2)^⌊u/2⌋₊ := rho_half_power (by linarith)
    _ = Real.exp (-(⌊u/2⌋₊:ℝ)*Real.log (u/2)) := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log ht0]
      exact one_div _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end NumberTheoryLean.DickmanFiniteDecay

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceBenchmarkDecay

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open Dickman DickmanFiniteDecay

theorem benchmark_deviation_le_gap (i : Side) {s : ℝ} (hs : 1 ≤ s) :
    |benchmark i s-1| ≤ gap s := by
  obtain ⟨hl,hu⟩ := deficits_pos hs
  have hsum := deficit_sum s
  cases i with
  | even =>
    have he : benchmark .even s-1 = -lowerDeficit s := by unfold benchmark lowerDeficit; ring
    rw [he,abs_neg,abs_of_pos hl]
    linarith
  | odd =>
    change |upperDeficit s| ≤ gap s
    rw [abs_of_pos hu]
    linarith

theorem gap_le_rho {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA*rho (s-1) := by
  rw [gap_eq_rho hs]
  exact div_le_self (mul_nonneg sieveA_pos.le (rho_nonneg _)) hs

theorem gap_le_constant {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA := by
  calc
    _ ≤ sieveA*rho (s-1) := gap_le_rho hs
    _ ≤ sieveA*1 := mul_le_mul_of_nonneg_left (rho_le_one _) sieveA_pos.le
    _ = _ := mul_one _

theorem boundary_rho_decay {r : ℝ} (hr : 18 ≤ r) :
    rho (r/2-1) ≤ Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  have hu : 8 ≤ r/2-1 := by linarith
  have hr0 : 0 < r := by linarith
  have hul : r/4 ≤ r/2-1 := by linarith
  have hlog : Real.log (r+2) ≤ 2*Real.log (r/2-1+2) := by
    have hp : 0 < r+2 := by linarith
    have hsq : r+2 ≤ (r/2-1+2)^2 := by nlinarith
    have hm := Real.log_le_log hp hsq
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hl0 : 0 ≤ Real.log (r+2)/2 := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hmul := mul_le_mul hul (show Real.log (r+2)/2 ≤ Real.log (r/2-1+2) by linarith)
    hl0 (by linarith : 0 ≤ r/2-1)
  calc
    _ ≤ Real.exp (-(1/16:ℝ)*(r/2-1)*Real.log (r/2-1+2)) := rho_log_decay hu
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem boundary_benchmark_decay : ∃ C : ℝ,0 < C ∧
    ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |benchmark i (r/2)-1| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  let C : ℝ := sieveA*Real.exp ((1/128:ℝ)*18*Real.log 20)
  have hC : 0 < C := mul_pos sieveA_pos (Real.exp_pos _)
  have hCA : sieveA ≤ C := by
    apply le_mul_of_one_le_right sieveA_pos.le
    apply Real.one_le_exp_iff.mpr
    positivity
  refine ⟨C,hC,?_⟩
  intro r hr i
  have hs : 1 ≤ r/2 := by linarith
  have hb := benchmark_deviation_le_gap i hs
  by_cases hlarge : 18 ≤ r
  · calc
      _ ≤ gap (r/2) := hb
      _ ≤ sieveA*rho (r/2-1) := gap_le_rho hs
      _ ≤ sieveA*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
        mul_le_mul_of_nonneg_left (boundary_rho_decay hlarge) sieveA_pos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hCA (Real.exp_nonneg _)
  · have hr18 : r ≤ 18 := le_of_lt (lt_of_not_ge hlarge)
    have hl : Real.log (r+2) ≤ Real.log 20 := Real.log_le_log (by linarith) (by linarith)
    have hm : r*Real.log (r+2) ≤ 18*Real.log 20 :=
      mul_le_mul hr18 hl (Real.log_nonneg (by linarith)) (by norm_num)
    have he : 1 ≤ Real.exp ((1/128:ℝ)*18*Real.log 20+(-(1/128:ℝ)*r*Real.log (r+2))) :=
      Real.one_le_exp_iff.mpr (by nlinarith)
    calc
      _ ≤ sieveA := hb.trans (gap_le_constant hs)
      _ ≤ sieveA*Real.exp ((1/128:ℝ)*18*Real.log 20+(-(1/128:ℝ)*r*Real.log (r+2))) :=
        le_mul_of_one_le_right sieveA_pos.le he
      _ = _ := by dsimp only [C]; rw [Real.exp_add]; ring

end NumberTheoryLean.ReferenceBenchmarkDecay



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem gap_append (w r : ℝ) (ps qs : List ℕ) :
    primeFinalGap w r (ps++qs)=primeFinalGap w (primeFinalGap w r ps) qs := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih => exact ih (r-primeExponent w p)

theorem admitted_append (w r : ℝ) (i : Side) (ps qs : List ℕ) :
    admitted w i r (ps++qs) ↔ admitted w i r ps ∧ admitted w (endSide i ps) (primeFinalGap w r ps) qs := by
  induction ps generalizing i r with
  | nil => simp only [List.nil_append,admitted,primeFinalGap,endSide,true_and]
  | cons p ps ih =>
    simp only [List.cons_append,admitted,endSide,primeFinalGap,ih,and_assoc]

theorem firstOmitted_not_admitted {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) : ¬admitted w i r ps := by
  rcases hp with ⟨pre,p,rfl,hpre,hfail⟩
  rw [admitted_append]
  intro h
  exact hfail h.2.1

theorem exists_first_omitted_prefix {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : ¬admitted w i r ps) :
    ∃ pre suf : List ℕ,ps=pre++suf ∧ FirstOmitted w i r pre := by
  induction ps generalizing i r with
  | nil => exact False.elim (hp trivial)
  | cons p ps ih =>
    by_cases hchild : childAdmitted i r (primeExponent w p)
    · have ht : ¬admitted w i.flip (r-primeExponent w p) ps := fun h => hp ⟨hchild,h⟩
      obtain ⟨pre,suf,he,hfirst⟩ := ih ht
      rcases hfirst with ⟨pre',q,hpre',ha,hbad⟩
      refine ⟨p::pre,suf,by rw [List.cons_append,he],?_⟩
      refine ⟨p::pre',q,by rw [List.cons_append,hpre'],⟨hchild,ha⟩,?_⟩
      exact hbad
    · exact ⟨[p],ps,rfl,[],p,rfl,trivial,hchild⟩

theorem firstOmitted_boundary_gap {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    primeFinalGap w r ps < 4 := by
  rcases hp with ⟨pre,p,rfl,_hpre,hfail⟩
  have hp2 : primeExponent w p ≤ 2 := hupper p (by simp)
  rw [gap_append]
  change primeFinalGap w r pre-primeExponent w p < 4
  cases he : endSide i pre with
  | even =>
    simp only [he,childAdmitted] at hfail
    exact False.elim (hfail trivial)
  | odd =>
    rw [he] at hfail
    change ¬max (2*primeExponent w p) (primeExponent w p+2) ≤ primeFinalGap w r pre-primeExponent w p at hfail
    have hmax : max (2*primeExponent w p) (primeExponent w p+2)=primeExponent w p+2 :=
      max_eq_right (by linarith)
    rw [hmax] at hfail
    linarith

theorem gap_lower_by_length {w r : ℝ} {ps : List ℕ}
    (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    r-2*(ps.length:ℝ) ≤ primeFinalGap w r ps := by
  induction ps generalizing r with
  | nil => simp [primeFinalGap]
  | cons p ps ih =>
    have hp := hupper p (by simp)
    have ht := ih (r:=r-primeExponent w p) (fun q hq => hupper q (by simp [hq]))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,primeFinalGap]
    linarith

theorem firstOmitted_boundary_length {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    (r-4)/2 < (ps.length:ℝ) := by
  have hg := firstOmitted_boundary_gap hp hupper
  have hl := gap_lower_by_length (r:=r) hupper
  linarith

theorem boundary_prime_exponent_upper {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p ∈ boundaryPrimes w) :
    primeExponent w p ≤ 2 := by
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hfloor,hprime⟩ := Nat.mem_primesLE.mp hpp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  apply (exponent_le_iff hw hp0).mpr
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mp hfloor

theorem actual_first_omission_length {w r : ℝ} (hw : 1 < w) (i : Side) {ps : List ℕ}
    (hp : ps ∈ firstOmissions w (boundaryPrimes w) i r) : (r-4)/2 < (ps.length:ℝ) := by
  classical
  obtain ⟨hfamily,hfirst⟩ := Finset.mem_filter.mp hp
  have hmem := (mem_decreasingPrefixes.mp hfamily).2
  exact firstOmitted_boundary_length hfirst (fun p hp => boundary_prime_exponent_upper hw (hmem p hp))

end NumberTheoryLean.ReferenceAdmission


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundaryPrimeMass
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceProductsBasics.availablePrimes_closed _root_.OAI.Erdos970.NumberTheoryLean.ReferenceSourcePrimeSets.sourcePrimes_boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.VariablePrimeTilt

open _root_.Finset
open ReferenceAdmission FinitePathGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem variable_tilt_weight (t : ℝ) (ps : List ℕ) :
    (ps.map (fun p : ℕ => t*(p:ℝ)⁻¹)).prod=t^ps.length*prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,prefixWeight] at ih ⊢
    rw [ih]
    ring

theorem long_prefix_variable_tilt (P : Finset ℕ) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    longPrefixMass P m ≤ Real.exp (t*∑ p ∈ P,(p:ℝ)⁻¹)/t^m := by
  have ht0 : 0 < t := by linarith
  apply (le_div_iff₀ (pow_pos ht0 m)).mpr
  rw [mul_comm,longPrefixMass,Finset.mul_sum]
  calc
    _ ≤ ∑ ps ∈ (decreasingPrefixes P).filter (fun ps => m ≤ ps.length),t^ps.length*prefixWeight ps := by
      apply Finset.sum_le_sum
      intro ps hp
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (Finset.mem_filter.mp hp).2) (prefixWeight_nonneg ps)
    _ ≤ ∑ ps ∈ decreasingPrefixes P,t^ps.length*prefixWeight ps := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ps _ _
      exact mul_nonneg (pow_nonneg ht0.le _) (prefixWeight_nonneg ps)
    _ = ∏ p ∈ P,(1+t*(p:ℝ)⁻¹) := by
      simp_rw [← variable_tilt_weight t]
      exact sum_sorted_products P _
    _ ≤ ∏ p ∈ P,Real.exp (t*(p:ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p _hp
        simpa only [add_comm] using Real.add_one_le_exp (t*(p:ℝ)⁻¹)
    _ = _ := by rw [← Real.exp_sum,← Finset.mul_sum]

theorem omission_mass_le_long {w r : ℝ} (hw : 1 < w) (hr : 4 ≤ r) (i : Side) :
    omissionMass w r i ≤ longPrefixMass (boundaryPrimes w) (⌊(r-4)/2⌋₊+1) := by
  classical
  unfold omissionMass longPrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    have hlen := actual_first_omission_length hw i hp
    have hf : ((⌊(r-4)/2⌋₊:ℕ):ℝ) < (ps.length:ℝ) :=
      (Nat.floor_le (by linarith : 0 ≤ (r-4)/2)).trans_lt hlen
    have hn : ⌊(r-4)/2⌋₊+1 ≤ ps.length := by
      have hh : ⌊(r-4)/2⌋₊ < ps.length := by exact_mod_cast hf
      omega
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,hn⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

theorem actual_omission_variable_tilt {w r t : ℝ} (hw : 1 < w) (hr : 4 ≤ r) (ht : 1 ≤ t) (i : Side) :
    omissionMass w r i ≤ Real.exp (t*∑ p ∈ boundaryPrimes w,(p:ℝ)⁻¹)/t^(⌊(r-4)/2⌋₊+1) :=
  (omission_mass_le_long hw hr i).trans (long_prefix_variable_tilt _ _ ht)

end NumberTheoryLean.VariablePrimeTilt

end

section

namespace NumberTheoryLean.BoundaryPrimeMass

open _root_.Finset
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem prime_sum_le_prefix_mass (P : Finset ℕ) :
    (∑ p ∈ P,(p:ℝ)⁻¹) ≤ ∑ ps ∈ decreasingPrefixes P,prefixWeight ps := by
  classical
  have hsub : P.image (fun p => [p]) ⊆ decreasingPrefixes P := by
    intro ps hps
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hps
    apply mem_decreasingPrefixes.mpr
    constructor
    · simp
    · intro q hq
      simpa using List.mem_singleton.mp hq ▸ hp
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ps _ _ => prefixWeight_nonneg ps)
  have he : (∑ ps ∈ P.image (fun p => [p]),prefixWeight ps) = ∑ p ∈ P,(p:ℝ)⁻¹ := by
    rw [Finset.sum_image]
    · simp [prefixWeight]
    · intro p _ q _ hpq
      simpa using hpq
  rwa [he] at h

theorem uniform_boundary_mass : ∃ T w₀ : ℝ,0 < T ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w →
      (∑ p ∈ boundaryPrimes w,(p:ℝ)⁻¹) ≤ T ∧
      (∑ ps ∈ decreasingPrefixes (boundaryPrimes w),prefixWeight ps) ≤ T ∧
      ∀ r i,omissionMass w r i ≤ T := by
  classical
  obtain ⟨M,w₀,hM,hw₀,h⟩ := total_prime_prefix_mass
  refine ⟨2*M,w₀,by positivity,hw₀,?_⟩
  intro w hw
  have hmass : (∑ ps ∈ decreasingPrefixes (boundaryPrimes w),prefixWeight ps) ≤ 2*M := by
    simpa [boundaryPrimes,Real.rpow_one,mul_comm] using h w hw 1 2 le_rfl (by norm_num)
  refine ⟨(prime_sum_le_prefix_mass _).trans hmass,hmass,?_⟩
  intro r i
  apply le_trans _ hmass
  unfold omissionMass firstOmissions
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ps _ _ => prefixWeight_nonneg ps)

end NumberTheoryLean.BoundaryPrimeMass

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FirstOmissionAntichain
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
open FinitePathGeometry ReferenceAdmission

theorem admitted_prefix {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hpre : pre <+: whole) (hwhole : admitted w i r whole) : admitted w i r pre := by
  obtain ⟨suf,he⟩ := hpre
  rw [← he,admitted_append] at hwhole
  exact hwhole.1

theorem proper_prefix_admitted {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hfirst : FirstOmitted w i r whole) (hpre : pre <+: whole)
    (hlen : pre.length < whole.length) : admitted w i r pre := by
  obtain ⟨parent,p,he,hparent,_⟩ := hfirst
  have hpar : parent <+: whole := ⟨[p],he.symm⟩
  have hlen' : pre.length ≤ parent.length := by
    rw [he,List.length_append,List.length_singleton] at hlen
    omega
  exact admitted_prefix (List.prefix_of_prefix_length_le hpre hpar hlen') hparent

theorem first_omission_antichain {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hp : FirstOmitted w i r pre) (hq : FirstOmitted w i r whole)
    (hpre : pre <+: whole) : pre = whole := by
  by_contra hne
  have hlenle := hpre.length_le
  have hlenne : pre.length ≠ whole.length := fun h => hne (hpre.eq_of_length h)
  have hlen : pre.length < whole.length := by omega
  exact firstOmitted_not_admitted hp (proper_prefix_admitted hq hpre hlen)

theorem first_omission_prefix_unique {w r : ℝ} {i : Side} {p q whole : List ℕ}
    (hp : FirstOmitted w i r p) (hq : FirstOmitted w i r q)
    (hpref : p <+: whole) (hqref : q <+: whole) : p = q := by
  rcases List.prefix_or_prefix_of_prefix hpref hqref with h | h
  · exact first_omission_antichain hp hq h
  · exact (first_omission_antichain hq hp h).symm

end NumberTheoryLean.ReferencePruning

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

theorem decreasing_prefix_mem {P : Finset ℕ} {pre suf : List ℕ}
    (h : pre++suf ∈ decreasingPrefixes P) : pre ∈ decreasingPrefixes P := by
  obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
  exact mem_decreasingPrefixes.mpr ⟨(List.pairwise_append.mp hp).1,
    fun p hpre => hm p (List.mem_append.mpr (Or.inl hpre))⟩

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_OmissionPartition
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
open FinitePathGeometry ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass

theorem rejected_eq_omission_completions (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    rejectedPrefixes w P i r = (firstOmissions w P i r).biUnion (completions P) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hD,hnot⟩ := Finset.mem_filter.mp hp
    obtain ⟨pre,suf,he,hfirst⟩ := exists_first_omitted_prefix hnot
    have hjoin : pre++suf ∈ decreasingPrefixes P := by rwa [← he]
    have hpre := decreasing_prefix_mem hjoin
    have hsuf := (append_mem_decreasing_iff hpre).mp hjoin
    apply Finset.mem_biUnion.mpr
    exact ⟨pre,Finset.mem_filter.mpr ⟨hpre,hfirst⟩,
      Finset.mem_image.mpr ⟨suf,hsuf,he.symm⟩⟩
  · intro hp
    obtain ⟨pre,hpre,hcomplete⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨suf,hsuf,rfl⟩ := Finset.mem_image.mp hcomplete
    obtain ⟨hD,hfirst⟩ := Finset.mem_filter.mp hpre
    apply Finset.mem_filter.mpr
    refine ⟨(append_mem_decreasing_iff hD).mpr hsuf,?_⟩
    intro hallowed
    exact firstOmitted_not_admitted hfirst ((admitted_append w r i pre suf).mp hallowed).1

theorem omission_completions_disjoint (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    (firstOmissions w P i r : Set (List ℕ)).PairwiseDisjoint (completions P) := by
  intro pre hpre other hother hne
  apply Finset.disjoint_left.mpr
  intro whole hp hq
  obtain ⟨suf,_,he⟩ := Finset.mem_image.mp hp
  obtain ⟨tail,_,hf⟩ := Finset.mem_image.mp hq
  have h := first_omission_prefix_unique (Finset.mem_filter.mp hpre).2
    (Finset.mem_filter.mp hother).2 (show pre <+: whole from ⟨suf,he⟩)
    (show other <+: whole from ⟨tail,hf⟩)
  exact hne h

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceSourcePrimeSets.sourcePrimes_boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem signedWeight_append (pre suf : List ℕ) : signedWeight (pre++suf) = signedWeight pre*signedWeight suf := by
  unfold signedWeight prefixWeight
  rw [List.length_append,pow_add,List.map_append,List.prod_append]
  ring

theorem sum_signedWeight (P : Finset ℕ) :
    (∑ ps ∈ decreasingPrefixes P,signedWeight ps) = survivorProduct P := by
  have h := sum_sorted_products P (fun p : ℕ => (-1 : ℝ)*(p : ℝ)⁻¹)
  simp_rw [VariablePrimeTilt.variable_tilt_weight] at h
  simpa only [signedWeight,survivorProduct,neg_one_mul,sub_eq_add_neg] using h

theorem sum_completion_signedWeight (P : Finset ℕ) (pre : List ℕ) :
    (∑ ps ∈ completions P pre,signedWeight ps) = signedWeight pre*survivorProduct (suffixPrimes P pre) := by
  unfold completions
  rw [Finset.sum_image]
  · simp_rw [signedWeight_append]
    rw [← Finset.mul_sum,sum_signedWeight]
  · intro a _ b _ h
    exact List.append_cancel_left h

end NumberTheoryLean.ReferencePruning

end

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open FinitePathGeometry ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass

theorem product_minus_reference (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    survivorProduct P-referencePolynomial w P i r =
      ∑ ps ∈ rejectedPrefixes w P i r,signedWeight ps := by
  have h := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (admitted w i r) signedWeight
  rw [sum_signedWeight] at h
  have he : referencePolynomial w P i r + (∑ ps ∈ rejectedPrefixes w P i r,signedWeight ps) =
      survivorProduct P := by
    simpa only [referencePolynomial,referencePrefixes,rejectedPrefixes,signedWeight] using h
  linarith only [he]

theorem pruning_identity (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    survivorProduct P-referencePolynomial w P i r =
      ∑ pre ∈ firstOmissions w P i r,signedWeight pre*survivorProduct (suffixPrimes P pre) := by
  rw [product_minus_reference,rejected_eq_omission_completions,
    Finset.sum_biUnion (omission_completions_disjoint w P i r)]
  exact Finset.sum_congr rfl (fun pre _ => sum_completion_signedWeight P pre)

end NumberTheoryLean.ReferencePruning

end

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem reciprocal_le_one {p : ℕ} (hp : 1 ≤ p) : (p : ℝ)⁻¹ ≤ 1 := by
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
  simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h

theorem survivorProduct_bounds (P : Finset ℕ) (hP : ∀ p ∈ P,1 ≤ p) :
    0 ≤ survivorProduct P ∧ survivorProduct P ≤ 1 := by
  have h0 : ∀ p ∈ P,0 ≤ 1-(p : ℝ)⁻¹ := fun p hp => sub_nonneg.mpr (reciprocal_le_one (hP p hp))
  have h1 : ∀ p ∈ P,1-(p : ℝ)⁻¹ ≤ 1 := fun p _ =>
    sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  exact ⟨Finset.prod_nonneg h0,Finset.prod_le_one h0 h1⟩

theorem abs_signedWeight (ps : List ℕ) : |signedWeight ps| = prefixWeight ps := by
  simp only [signedWeight,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (prefixWeight_nonneg ps)]

theorem pruning_discrepancy_bound (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ)
    (hP : ∀ p ∈ P,1 ≤ p) :
    |referencePolynomial w P i r-survivorProduct P| ≤
      ∑ ps ∈ firstOmissions w P i r,prefixWeight ps := by
  rw [abs_sub_comm,pruning_identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro pre _hpre
  have hprod := survivorProduct_bounds (suffixPrimes P pre)
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
  rw [abs_mul,abs_signedWeight,abs_of_nonneg hprod.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod.2 (prefixWeight_nonneg pre)

theorem boundary_reference_discrepancy (w r : ℝ) (i : Side) :
    |referencePolynomial w (boundaryPrimes w) i r-
      (∏ p ∈ boundaryPrimes w,(1-(p : ℝ)⁻¹))| ≤ omissionMass w r i := by
  apply pruning_discrepancy_bound w (boundaryPrimes w) i r
  intro p hp
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  exact le_trans (by norm_num : 1 ≤ 2) (Nat.mem_primesLE.mp hpp).2.two_le

end NumberTheoryLean.ReferencePruning

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OmissionTiltDecay
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceSourcePrimeSets.sourcePrimes_boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OmissionTiltDecay

open _root_.Finset
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt BoundaryPrimeMass

theorem omission_depth_lower {r : ℝ} (hr : 8 ≤ r) :
    r/4 ≤ ((⌊(r-4)/2⌋₊+1:ℕ):ℝ) := by
  have hf := Nat.lt_floor_add_one ((r-4)/2)
  push_cast
  linarith

theorem sqrt_tilt_decay {T r : ℝ} (hT : 0 ≤ T) (hr : 8 ≤ r)
    (hlog : 1 ≤ Real.log r) (hlarge : (16*T)^2 ≤ r) :
    Real.exp (Real.sqrt r*T)/(Real.sqrt r)^(⌊(r-4)/2⌋₊+1) ≤
      Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs : 16*T ≤ Real.sqrt r := by
    have hsq := Real.sq_sqrt hr0.le
    nlinarith [Real.sqrt_nonneg r]
  have hmain : Real.sqrt r*T ≤ r/16 := by
    have hh := mul_le_mul_of_nonneg_right hs hs0.le
    nlinarith [Real.sq_sqrt hr0.le]
  have hlen := omission_depth_lower hr
  have hlog0 : 0 ≤ Real.log r := by linarith
  have hden : r*Real.log r/8 ≤
      ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r) := by
    rw [Real.log_sqrt hr0.le]
    nlinarith [mul_le_mul_of_nonneg_right hlen hlog0]
  have hlog2 : Real.log (r+2) ≤ 2*Real.log r := by
    have hh : r+2 ≤ r^2 := by nlinarith
    have hm := Real.log_le_log (by linarith : 0 < r+2) hh
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hpay : r/16 ≤ r*Real.log r/16 := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hr0.le]
  have hcompare : Real.sqrt r*T-
      ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r) ≤
      -(1/32:ℝ)*r*Real.log (r+2) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hr0.le]
  calc
    _ = Real.exp (Real.sqrt r*T-
        ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r)) := by
      rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hs0]
    _ ≤ _ := Real.exp_le_exp.mpr hcompare

theorem actual_omission_decay : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      omissionMass w r i ≤ C*Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
  obtain ⟨T,w₀,hT,hw₀,hbound⟩ := uniform_boundary_mass
  let R : ℝ := max 8 (max (Real.exp 1) ((16*T)^2))
  have hR8 : 8 ≤ R := le_max_left _ _
  have hRe : Real.exp 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRT : (16*T)^2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  let C : ℝ := max 1 (T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCT : T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)) ≤ C := le_max_right _ _
  refine ⟨C,w₀,by linarith,hw₀,?_⟩
  intro w hw r hr i
  obtain ⟨hp,_hm,ho⟩ := hbound w hw
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr0 : 0 < r := by linarith
  by_cases hbig : R ≤ r
  · have hr8 := hR8.trans hbig
    have hl : 1 ≤ Real.log r := by
      have hh := Real.log_le_log (Real.exp_pos 1) (hRe.trans hbig)
      simpa using hh
    have ht : 1 ≤ Real.sqrt r := (Real.one_le_sqrt).mpr (by linarith)
    have hv := actual_omission_variable_tilt hw1 (by linarith : 4 ≤ r) ht i
    have hnum := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg r))
    calc
      _ ≤ Real.exp (Real.sqrt r*T)/(Real.sqrt r)^(⌊(r-4)/2⌋₊+1) :=
        hv.trans (div_le_div_of_nonneg_right hnum (pow_nonneg (Real.sqrt_nonneg r) _))
      _ ≤ Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := sqrt_tilt_decay hT.le hr8 hl (hRT.trans hbig)
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_nonneg _) hC1
  · have hrR : r ≤ R := le_of_lt (lt_of_not_ge hbig)
    have hl0 : 0 ≤ Real.log (r+2) := Real.log_nonneg (by linarith)
    have hlR : Real.log (r+2) ≤ Real.log (R+2) := Real.log_le_log (by linarith) (by linarith)
    have hprod : r*Real.log (r+2) ≤ R*Real.log (R+2) :=
      mul_le_mul hrR hlR hl0 (by linarith)
    have hh : (1/32:ℝ)*R*Real.log (R+2) + (-(1/32:ℝ)*r*Real.log (r+2)) ≥ 0 := by nlinarith
    have he := Real.one_le_exp_iff.mpr hh
    calc
      _ ≤ T := ho r i
      _ ≤ T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)+(-(1/32:ℝ)*r*Real.log (r+2))) :=
        le_mul_of_one_le_right hT.le he
      _ = (T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)))*Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCT (Real.exp_nonneg _)

end NumberTheoryLean.OmissionTiltDecay

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

namespace NumberTheoryLean.BoundaryAnomaly

open FinitePathGeometry ReferenceAdmission ReferencePruning
open VariablePrimeTilt OmissionTiltDecay ReferenceBenchmarkDecay

theorem boundary_product_bounds (w : ℝ) :
    0 ≤ survivorProduct (boundaryPrimes w) ∧ survivorProduct (boundaryPrimes w) ≤ 1 := by
  apply survivorProduct_bounds
  intro p hp
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  exact (by norm_num : 1 ≤ 2).trans (Nat.mem_primesLE.mp hpp).2.two_le

theorem anomaly_le_omission_and_benchmark (w r : ℝ) (i : Side) :
    |anomaly w i r| ≤ omissionMass w r i+|benchmark i (r/2)-1| := by
  have hp := boundary_product_bounds w
  have hd := boundary_reference_discrepancy w r i
  have he : anomaly w i r =
      (referencePolynomial w (boundaryPrimes w) i r-survivorProduct (boundaryPrimes w))-
        survivorProduct (boundaryPrimes w)*(benchmark i (r/2)-1) := by
    unfold anomaly
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hp.1]
  exact add_le_add hd (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _))

theorem actual_boundary_anomaly_decay : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  obtain ⟨CO,w₀,hCO,hw₀,hO⟩ := actual_omission_decay
  obtain ⟨CB,hCB,hB⟩ := boundary_benchmark_decay
  refine ⟨CO+CB,w₀,by positivity,hw₀,?_⟩
  intro w hw r hr i
  have hr0 : 0 ≤ r := by linarith
  have hl0 : 0 ≤ Real.log (r+2) := Real.log_nonneg (by linarith)
  have he : Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) ≤
      Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr0 hl0])
  calc
    _ ≤ omissionMass w r i+|benchmark i (r/2)-1| := anomaly_le_omission_and_benchmark w r i
    _ ≤ CO*Real.exp (-(1/32:ℝ)*r*Real.log (r+2))+
        CB*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := add_le_add (hO w hw r hr i) (hB r hr i)
    _ ≤ CO*Real.exp (-(1/128:ℝ)*r*Real.log (r+2))+
        CB*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left he hCO.le) _
    _ = _ := by ring

theorem actual_boundary_anomaly_exponential : ∃ C c w₀ : ℝ,0 < C ∧ 0 < c ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-c*r) := by
  obtain ⟨C,w₀,hC,hw₀,h⟩ := actual_boundary_anomaly_decay
  refine ⟨C,Real.log 4/128,w₀,hC,div_pos (Real.log_pos (by norm_num)) (by norm_num),hw₀,?_⟩
  intro w hw r hr i
  have hl : Real.log 4 ≤ Real.log (r+2) := Real.log_le_log (by norm_num) (by linarith)
  apply (h w hw r hr i).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ r)]

end NumberTheoryLean.BoundaryAnomaly

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_UniformExponentialOccupation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformExponentialOccupation

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open UncappedCompactMass LiteralUniformPrimeTail LiteralPrimeOccupation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem compact_tail_split {c : ℝ} (hc : 0 < c) (K w ell : ℝ) (start : Node) :
    exponentialPrefixMass c w ell start ≤ compactPrefixMass K w ell start+
      ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*tailListReward c K w start ps := by
  unfold exponentialPrefixMass compactPrefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ps _hp
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (prefixWeight_nonneg ps)
  unfold positiveGapEnvelope tailListReward
  by_cases hr : 2 ≤ (terminal w start ps).gap
  · rw [ite_eq_left hr]
    by_cases hK : (terminal w start ps).gap ≤ K
    · rw [ite_eq_left ⟨hr,hK⟩,ite_eq_right (not_lt_of_ge hK)]
      simpa only [add_zero] using Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by linarith))
    · rw [ite_eq_right (fun h => hK h.2),ite_eq_left (lt_of_not_ge hK),zero_add]
  · rw [ite_eq_right hr,ite_eq_right (fun h => hr h.1),zero_add]
    split_ifs <;> positivity

theorem uniform_exponential_prefix_mass (ell c d : ℝ) (hell : 1 ≤ ell) (hc : 0 < c) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*exponentialPrefixMass c w ell start ≤ C := by
  obtain ⟨M,BT,wT,hBT,hwT,htail⟩ := actual_uniform_original_prime_tail d c 1 hd hc (by norm_num)
  let K : ℝ := 3*((M:ℝ)+1)
  have hK : 3 ≤ K := by dsimp [K]; have hn := Nat.cast_nonneg (α:=ℝ) M; linarith
  obtain ⟨CC,BC,wC,hCC,hBC,hwC,hcompact⟩ := uniform_uncapped_compact_mass K ell d hK hell hd
  refine ⟨CC+1,max BC (max BT ell),max wC wT,by linarith,
    hBC.trans_le (le_max_left _ _),hwC.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBC' : BC ≤ B := (le_max_left _ _).trans hB
  have hBT' : BT ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hellB : ell ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have hwC' : wC ≤ w := (le_max_left _ _).trans hw
  have hwT' : wT ≤ w := (le_max_right _ _).trans hw
  have ht := htail M le_rfl B w hBT' hwT' ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hcc := hcompact B w hBC' hwC' hcomp start hi h199 h23 hcons hcut
  have hsplit := mul_le_mul_of_nonneg_left (compact_tail_split hc K w ell start) (sq_nonneg B)
  dsimp only [K] at hsplit hcc
  nlinarith

theorem uniform_signed_exponential_rewards (ell c d : ℝ) (hell : 1 ≤ ell) (hc : 0 < c) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → ∀ A : ℝ,0 ≤ A → ∀ F : List ℕ → ℝ,
          (∀ ps ∈ uncappedPrefixes w ell start,|F ps| ≤ A*positiveGapEnvelope c (terminal w start ps).gap) →
          B^2*|∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps| ≤ A*C := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,h⟩ := uniform_exponential_prefix_mass ell c d hell hc hd
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut A hA F hF
  have hmass := h B w hB hw hcomp start hi h199 h23 hcons hcut
  have hab : |∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps| ≤
      A*exponentialPrefixMass c w ell start := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [exponentialPrefixMass,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hp
    rw [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
    have hm := mul_le_mul_of_nonneg_left (hF ps hp) (prefixWeight_nonneg ps)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm := mul_le_mul_of_nonneg_left hab (sq_nonneg B)
  have hfinal := mul_le_mul_of_nonneg_left hmass hA
  nlinarith

end NumberTheoryLean.UniformExponentialOccupation

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

section

namespace NumberTheoryLean.UniformBoundaryCorrection

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open BoundaryAnomaly UniformExponentialOccupation ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass

theorem uniform_boundary_correction (ell d : ℝ) (hell : 2 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*|boundaryCorrection w ell start| ≤ C := by
  obtain ⟨A,c,wA,hA,hc,hwA,hAnomaly⟩ := actual_boundary_anomaly_exponential
  obtain ⟨CP,BP,wP,hCP,hBP,hwP,hOccupation⟩ :=
    uniform_signed_exponential_rewards ell c d (by linarith) hc hd
  refine ⟨A*CP,max BP 4,max wP wA,mul_pos hA hCP,hBP.trans_le (le_max_left _ _),
    hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBP' : BP ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hwP' : wP ≤ w := (le_max_left _ _).trans hw
  have hwA' : wA ≤ w := (le_max_right _ _).trans hw
  apply hOccupation B w hBP' hwP' hcomp start hi h199 h23 hcons hcut A hA.le
    (fun ps => (-1:ℝ)^ps.length*anomaly w (terminal w start ps).side (terminal w start ps).gap)
  intro ps hp
  have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
  have hdom := source_boundary_domain hB4 hell start hi h199 h23 hcons hcut hpA
  have hr2 := boundary_gap_ge_two hdom
  rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,positiveGapEnvelope,ite_eq_left hr2]
  exact hAnomaly w hwA' _ hr2 _

theorem uniform_boundary_correction_div_jb247_oai (ell d : ℝ) (hell : 2 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → |boundaryCorrection w ell start| ≤ C/B^2 := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,h⟩ := uniform_boundary_correction ell d hell hd
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  apply (le_div_iff₀ (sq_pos_of_pos (hB₀.trans_le hB))).mpr
  simpa only [mul_comm] using h B w hB hw hcomp start hi h199 h23 hcons hcut

end NumberTheoryLean.UniformBoundaryCorrection

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247_oai := @OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247_oai
