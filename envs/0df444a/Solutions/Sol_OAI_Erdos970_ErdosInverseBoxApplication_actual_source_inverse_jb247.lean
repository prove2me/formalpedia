-- Prove2me | solution 1 for OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:26.212734+00:00
-- url     : https://prove2.me/submissions/d81d039e-0eaf-4a0d-84ee-32372fb154c6

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
import Definitions.Def_OAIQ247J008
import Theorems.Thm_OAI_Erdos970_ErdosInverseRefinement_source_no_dense_cell_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinCounting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin

theorem primeBin_log_sum {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) :
    (∑ p ∈ primeBin R xi,Real.log p) = Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R := by
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊(1+xi)*R⌋₊ := by
    intro p hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_mono (by nlinarith)),hprime⟩
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
  simpa only [primeBin] using (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p) hsub)

theorem primeBin_log_sum_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (∑ p ∈ primeBin R xi,Real.log p) ≤ (primeBin R xi).card*(2*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hupper : (1+xi)*R ≤ R^2 := by nlinarith
  have hb0 : 0 < (1+xi)*R := by positivity
  have hlog : Real.log ((1+xi)*R) ≤ 2*Real.log R := by
    have h := Real.log_le_log hb0 hupper
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ _p ∈ primeBin R xi,2*Real.log R := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime,_,hhi⟩ := (mem_primeBin hR0.le hxi p).mp hp
      exact (Real.log_le_log (by exact_mod_cast hprime.pos) hhi).trans hlog
    _ = _ := by simp

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosInversePrimeBin
open _root_.Filter _root_.Asymptotics
open scoped Topology
open ErdosPrimeInputs.StrongChebyshev ErdosPrimeInputs.PrimeErrorDecay

theorem prime_bin_theta_error : ∃ c C R₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ R : ℝ,R₀ ≤ R → ∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ 3*C*R*decay c R := by
  obtain ⟨c,hc,hstrong⟩ := theta_strong
  obtain ⟨C,hC,hbig⟩ := hstrong.exists_pos
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbig.bound
  refine ⟨c,C,max A 2,hc,hC,le_max_right _ _,?_⟩
  intro R hR xi hxi hxi1
  have hR2 : 2 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hbR : R ≤ (1+xi)*R := by nlinarith
  have hb2 : (1+xi)*R ≤ 2*R := by nlinarith
  have htheta (x : ℝ) (hx : A ≤ x) (hx0 : 0 ≤ x) :
      |Chebyshev.theta x-x| ≤ C*(x*decay c x) := by
    have h := hA x hx
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (errorScale_nonneg c hx0)] at h
    exact h
  have hr := htheta R hRA hR0.le
  have hb : |Chebyshev.theta ((1+xi)*R)-(1+xi)*R| ≤ 2*C*R*decay c R := by
    calc
      _ ≤ C*(((1+xi)*R)*decay c ((1+xi)*R)) := htheta _ (hRA.trans hbR) (hR0.le.trans hbR)
      _ ≤ C*((2*R)*decay c R) := mul_le_mul_of_nonneg_left
        (mul_le_mul hb2 (decay_antitone hc.le hR0 hbR) (decay_pos _ _).le (by positivity)) hC.le
      _ = _ := by ring
  have he : Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R =
      (Chebyshev.theta ((1+xi)*R)-(1+xi)*R)-(Chebyshev.theta R-R) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith only [hb,hr])

theorem decay_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (decay c) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,decay,neg_mul]

theorem uniform_bin_theta_error {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ xi*R/2 := by
  obtain ⟨c,C,R₀,hc,hC,hR₀,hbound⟩ := prime_bin_theta_error
  have hdec : Tendsto (fun R : ℝ => 3*C*decay c R) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decay_tendsto_zero hc).const_mul (3*C)
  filter_upwards [eventually_ge_atTop R₀,
    hdec.eventually (eventually_le_nhds (show 0 < eta/2 by positivity))] with R hR hd
  have hR2 := hR₀.trans hR
  refine ⟨hR2,?_⟩
  intro xi hxi hxi1
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have he := hbound R hR xi hxi0 hxi1
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ R by linarith)
  have hwidth := mul_le_mul_of_nonneg_right hxi (show 0 ≤ R by linarith)
  exact he.trans (by nlinarith only [hm,hwidth])

end ErdosInversePrimeBin



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FactorDividesAbscissa
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInverseIncidence
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem sum_bit {α β : Type*} (P : Finset β) (R : α → β → Prop) (a : α) :
    (∑ p ∈ P,bit R a p) = (degree P R a : ℝ) := by
  exact Finset.sum_boole (R a) P

theorem sum_bit_product {α β : Type*} (P : Finset β) (R : α → β → Prop) (a b : α) :
    (∑ p ∈ P,bit R a p*bit R b p) = ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) := by
  have h (p : β) : bit R a p*bit R b p = if R a p ∧ R b p then (1 : ℝ) else 0 := by
    by_cases ha : R a p <;> by_cases hb : R b p <;> simp [bit,ha,hb]
  simp_rw [h]
  exact Finset.sum_boole _ _

theorem multiplicity_sum {α β : Type*} (A : Finset α) (P : Finset β) (R : α → β → Prop) :
    (∑ p ∈ P,multiplicity A R p) = ∑ a ∈ A,(degree P R a : ℝ) := by
  unfold multiplicity
  rw [Finset.sum_comm]
  simp_rw [sum_bit]

theorem multiplicity_square_sum {α β : Type*} (A : Finset α) (P : Finset β) (R : α → β → Prop) :
    (∑ p ∈ P,(multiplicity A R p)^2) =
      ∑ a ∈ A,∑ b ∈ A,((P.filter (fun p => R a p ∧ R b p)).card : ℝ) := by
  have h (p : β) : (multiplicity A R p)^2 = ∑ a ∈ A,∑ b ∈ A,bit R a p*bit R b p := by
    unfold multiplicity
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp_rw [sum_bit_product]

theorem multiplicity_square_upper {α β : Type*} (A : Finset α) (P : Finset β)
    (R : α → β → Prop) {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ P,(multiplicity A R p)^2) ≤ (A.card : ℝ)*(P.card : ℝ)+K*(A.card : ℝ)^2 := by
  rw [multiplicity_square_sum]
  calc
    _ ≤ ∑ a ∈ A,∑ b ∈ A,((if b=a then (P.card : ℝ) else 0)+K) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : b=a
      · rw [ite_eq_left hab]
        have hc : ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ P.card := by
          exact_mod_cast Finset.card_filter_le P (fun p => R a p ∧ R b p)
        linarith
      · rw [ite_eq_right hab,zero_add]
        exact hpair a ha b hb (Ne.symm hab)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const,nsmul_eq_mul]
      have he : (∑ a ∈ A,if a ∈ A then (P.card : ℝ) else 0) = (A.card : ℝ)*(P.card : ℝ) := by
        simp
      rw [he]
      ring

theorem dense_incidence_card_bound {α β : Type*} (A : Finset α) (P : Finset β)
    (R : α → β → Prop) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hP : 0 < P.card)
    (hdense : ∀ a ∈ A,c*(P.card : ℝ) ≤ (degree P R a : ℝ))
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K)
    (hlarge : 2*K ≤ c^2*(P.card : ℝ)) : (A.card : ℝ) ≤ 2/c^2 := by
  let M : ℝ := A.card
  let N : ℝ := P.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hP
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hlow : M*c*N ≤ ∑ p ∈ P,multiplicity A R p := by
    rw [multiplicity_sum]
    calc
      _ = ∑ _a ∈ A,c*N := by simp [M] <;> ring
      _ ≤ _ := Finset.sum_le_sum hdense
  have hcs : (∑ p ∈ P,multiplicity A R p)^2 ≤ N*(∑ p ∈ P,(multiplicity A R p)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ)) (multiplicity A R)
  have hup := multiplicity_square_upper A P R hK hpair
  have hchain : (M*c*N)^2 ≤ N*(M*N+K*M^2) :=
    (pow_le_pow_left₀ (by positivity) hlow 2).trans
      (hcs.trans (mul_le_mul_of_nonneg_left hup hN.le))
  have hmain : M^2*c^2*N ≤ M*N+K*M^2 := by
    have hscaled : (M^2*c^2*N)*N ≤ (M*N+K*M^2)*N := by
      first | (convert hchain using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hchain.trans (le_of_eq (by ring)))
    exact le_of_mul_le_mul_right hscaled hN
  have hKm : 2*K*M^2 ≤ c^2*N*M^2 := mul_le_mul_of_nonneg_right hlarge (sq_nonneg M)
  have hMN : M^2*c^2 ≤ 2*M := by
    have hscaled : (M^2*c^2)*N ≤ (2*M)*N := by nlinarith only [hmain,hKm]
    exact le_of_mul_le_mul_right hscaled hN
  change M ≤ 2/c^2
  by_cases hm : M=0
  · rw [hm]
    positivity
  · have hMp : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hm)
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    have hscaled : (M*c^2)*M ≤ 2*M := by convert hMN using 1 <;> first | rfl | ring
    exact le_of_mul_le_mul_right hscaled hMp

end ErdosInverseIncidence

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem determinant_ne_zero {q r : ℚ} (hqr : q ≠ r) : determinant q r ≠ 0 := by
  intro h
  apply hqr
  apply Rat.eq_iff_mul_eq_mul.mpr
  exact sub_eq_zero.mp h

theorem common_alignment_dvd (a : ℕ → ℤ) (q r : ℚ) (p : ℕ)
    (hq : aligns a q p) (hr : aligns a r p) : (p : ℤ) ∣ determinant q r := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have he : ((determinant q r : ℤ) : ZMod p) =
      (q.num : ZMod p)*(r.den : ZMod p)-(r.num : ZMod p)*(q.den : ZMod p) := by
    simp only [determinant,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  rw [he,← hq,← hr]
  ring

theorem determinant_height (q r : ℚ) (HA HD : ℕ)
    (hqa : q.num.natAbs ≤ HA) (hra : r.num.natAbs ≤ HA)
    (hqd : q.den ≤ HD) (hrd : r.den ≤ HD) :
    (determinant q r).natAbs ≤ 2*HA*HD := by
  calc
    _ ≤ (q.num*(r.den : ℤ)).natAbs+(r.num*(q.den : ℤ)).natAbs := Int.natAbs_sub_le _ _
    _ = q.num.natAbs*r.den+r.num.natAbs*q.den := by
      rw [Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]
    _ ≤ HA*HD+HA*HD := add_le_add (Nat.mul_le_mul hqa hrd) (Nat.mul_le_mul hra hqd)
    _ = _ := by ring

end ErdosInverseAlignment

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem mem_heightCandidates (HA HD : ℕ) (q : ℚ) :
    q ∈ heightCandidates HA HD ↔ q.num.natAbs ≤ HA ∧ q.den ≤ HD := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨ha,hd⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,ha,hd⟩
    apply Finset.mem_image.mpr
    refine ⟨(q.num,q.den),?_,?_⟩
    · apply Finset.mem_product.mpr
      have habs : |q.num| ≤ (HA : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast ha
      exact ⟨Finset.mem_Icc.mpr (abs_le.mp habs),
        Finset.mem_Icc.mpr ⟨q.den_pos,hd⟩⟩
    · exact q.num_div_den

theorem mem_rationalList (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (c : ℝ) (q : ℚ) :
    q ∈ rationalList P a HA HD c ↔
      q.num.natAbs ≤ HA ∧ q.den ≤ HD ∧
      c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ) := by
  simp only [rationalList,Finset.mem_filter,mem_heightCandidates,and_assoc]

end ErdosInverseAlignment

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRationalList
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem common_prime_product_dvd (P : Finset ℕ) (a : ℕ → ℤ) {q r : ℚ}
    (hqr : q ≠ r) (hP : ∀ p ∈ P,p.Prime) :
    (∏ p ∈ commonAligners P a q r,p) ∣ (determinant q r).natAbs := by
  have hn := Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr)
  have hsub : commonAligners P a q r ⊆ (determinant q r).natAbs.primeFactors := by
    intro p hp
    obtain ⟨hpP,hq,hr⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP,Int.natCast_dvd.mp (common_alignment_dvd a q r p hq hr),hn⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd _)

theorem common_primes_power_height_bound (P : Finset ℕ) (a : ℕ → ℤ) {q r : ℚ}
    (hqr : q ≠ r) (hP : ∀ p ∈ P,p.Prime) {z α C : ℝ}
    (hz : 1 < z) (hα : 0 < α) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((determinant q r).natAbs : ℝ) ≤ z^C) :
    ((commonAligners P a q r).card : ℝ) ≤ C/α := by
  have hprod : (∏ p ∈ commonAligners P a q r,p) ≤ (determinant q r).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr)))
      (common_prime_product_dvd P a hqr hP)
  have hpow : z^(α*((commonAligners P a q r).card : ℝ)) ≤ z^C := by
    calc
      _ = ∏ _p ∈ commonAligners P a q r,z^α := by
        rw [Finset.prod_const,Real.rpow_mul_natCast (by linarith : 0 ≤ z)]
      _ ≤ ∏ p ∈ commonAligners P a q r,(p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (by linarith) _)
          (fun p hp => hlarge p (Finset.mem_filter.mp hp).1)
      _ = ((∏ p ∈ commonAligners P a q r,p : ℕ) : ℝ) := by simp
      _ ≤ ((determinant q r).natAbs : ℝ) := by exact_mod_cast hprod
      _ ≤ _ := hheight
  have h := (Real.rpow_le_rpow_left_iff hz).mp hpow
  apply (le_div_iff₀ hα).mpr
  nlinarith only [h]

end ErdosInverseAlignment

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem prime_rational_list_bound (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ)
    {z α C c : ℝ} (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((2*HA*HD : ℕ) : ℝ) ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    ((rationalList P a HA HD c).card : ℝ) ≤ 2/c^2 := by
  apply ErdosInverseIncidence.dense_incidence_card_bound
    (rationalList P a HA HD c) P (fun q p => aligns a q p) hc (div_nonneg hC hα.le) hPpos
  · intro q hq
    exact (mem_rationalList P a HA HD c q).mp hq |>.2.2
  · intro q hq r hr hqr
    obtain ⟨hqa,hqd,_⟩ := (mem_rationalList P a HA HD c q).mp hq
    obtain ⟨hra,hrd,_⟩ := (mem_rationalList P a HA HD c r).mp hr
    apply common_primes_power_height_bound P a hqr hP hz hα hlarge
    exact (show ((determinant q r).natAbs : ℝ) ≤ ((2*HA*HD : ℕ) : ℝ) by
      exact_mod_cast determinant_height q r HA HD hqa hra hqd hrd).trans hheight
  · exact henough

theorem prime_rational_list_card_le_ceil (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ)
    {z α C c : ℝ} (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((2*HA*HD : ℕ) : ℝ) ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    (rationalList P a HA HD c).card ≤ ⌈2/c^2⌉₊ := by
  have h := (prime_rational_list_bound P a HA HD hz hα hC hc hP hlarge hheight hPpos henough).trans
    (Nat.le_ceil (2/c^2))
  exact_mod_cast h

end ErdosInverseAlignment

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualCollisionBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem mem_sourceRationalList (P : Finset ℕ) (a : ℕ → ℤ) {Sq R Z c : ℝ}
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) (q : ℚ) :
    q ∈ sourceRationalList P a Sq R Z c ↔
      (q.num.natAbs : ℝ) ≤ Sq*R*Z^10 ∧ (q.den : ℝ) ≤ R*Z^10 ∧
      c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ) := by
  rw [sourceRationalList,mem_rationalList,
    Nat.le_floor_iff (show 0 ≤ Sq*R*Z^10 by positivity),
    Nat.le_floor_iff (show 0 ≤ R*Z^10 by positivity)]

theorem source_height_product_bound {Sq R Z : ℝ}
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) :
    ((2*⌊Sq*R*Z^10⌋₊*⌊R*Z^10⌋₊ : ℕ) : ℝ) ≤ 2*Sq*R^2*Z^20 := by
  push_cast
  calc
    _ ≤ (2*(Sq*R*Z^10))*(R*Z^10) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num))
        (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem source_rational_list_bound (P : Finset ℕ) (a : ℕ → ℤ)
    {Sq R Z z α C c : ℝ} (hSq : 0 ≤ Sq) (hR : 0 ≤ R)
    (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : 2*Sq*R^2*Z^20 ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    (sourceRationalList P a Sq R Z c).card ≤ ⌈2/c^2⌉₊ := by
  exact prime_rational_list_card_le_ceil P a _ _ hz hα hC hc hP hlarge
    ((source_height_product_bound hSq hR).trans hheight) hPpos henough

end ErdosInverseAlignment



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRationalList
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem primeBin_log_sum_lower {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    (primeBin R xi).card*Real.log R ≤ ∑ p ∈ primeBin R xi,Real.log p := by
  calc
    _ = ∑ _p ∈ primeBin R xi,Real.log R := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log hR ((mem_primeBin hR.le hxi p).mp hp).2.1.le

theorem uniform_prime_bin_count {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      xi*R/(4*Real.log R) ≤ (primeBin R xi).card ∧
      (primeBin R xi).card ≤ 2*xi*R/Real.log R := by
  filter_upwards [uniform_bin_theta_error heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hR0 : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have he := hR.2 xi hxi hxi1
  rw [← primeBin_log_sum hR0.le hxi0] at he
  have hlow := (abs_le.mp he).1
  have hhigh := (abs_le.mp he).2
  have hcountupper := primeBin_log_sum_upper hR.1 hxi0 hxi1
  have hcountlower := primeBin_log_sum_lower hR0 hxi0
  constructor
  · apply (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    nlinarith only [hlow,hcountupper]
  · apply (le_div_iff₀ hlog).mpr
    have hprod := mul_nonneg hxi0 hR0.le
    nlinarith only [hhigh,hcountlower,hprod]

theorem log_le_two_sqrt {R : ℝ} (hR : 0 < R) : Real.log R ≤ 2*Real.sqrt R := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hR)
  have he : Real.log R = 2*Real.log (Real.sqrt R) := by
    rw [← Real.sq_sqrt hR.le,Real.log_pow]
    norm_num
  rw [he]
  linarith

theorem bin_scale_sqrt_lower {R xi eta : ℝ} (hR : 2 ≤ R) (heta : 0 < eta) (hxi : eta ≤ xi) :
    eta*Real.sqrt R/8 ≤ xi*R/(4*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (show 0 < 4*Real.log R by positivity)).mpr
  have hlogbound := mul_le_mul_of_nonneg_left (log_le_two_sqrt hR0)
    (show 0 ≤ eta*Real.sqrt R by positivity)
  have hRxi := mul_le_mul_of_nonneg_right hxi hR0.le
  have hs := Real.sq_sqrt hR0.le
  have he : eta*Real.sqrt R*(2*Real.sqrt R) = 2*eta*R := by
    calc
      _ = 2*eta*(Real.sqrt R)^2 := by ring
      _ = _ := by rw [hs]
  rw [he] at hlogbound
  nlinarith only [hlogbound,hRxi]

end ErdosInversePrimeBin

end

section

namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem uniform_prime_bin_many {eta : ℝ} (heta : 0 < eta) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 → N ≤ (primeBin R xi).card := by
  filter_upwards [uniform_prime_bin_count heta,
    eventually_ge_atTop ((8*(N : ℝ)/eta)^2)] with R hR hsize
  have hR0 : 0 < R := by linarith [hR.1]
  have hs : 8*(N : ℝ)/eta ≤ Real.sqrt R :=
    (Real.le_sqrt (by positivity) hR0.le).mpr hsize
  have hn : (N : ℝ) ≤ eta*Real.sqrt R/8 := by
    have h := (div_le_iff₀ heta).mp hs
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    nlinarith only [h]
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have h := hn.trans ((bin_scale_sqrt_lower hR.1 heta hxi).trans (hR.2 xi hxi hxi1).1)
  exact_mod_cast h

end ErdosInversePrimeBin

end

section

namespace ErdosInverseCells
open ErdosInversePrimeBin

theorem prime_bin_weight_spread (R theta xi : ℝ) (hR : 0 < R) (htheta : 0 ≤ theta)
    (hxi : 0 ≤ xi) (hthetaXi : theta ≤ xi) :
    ∀ p ∈ primeBin R theta,∀ r ∈ primeBin R theta,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹ := by
  intro p hp r hr
  have hpm := (mem_primeBin hR.le htheta p).mp hp
  have hrm := (mem_primeBin hR.le htheta r).mp hr
  have hp0 : (0 : ℝ) < p := hR.trans hpm.2.1
  have hr0 : (0 : ℝ) < r := hR.trans hrm.2.1
  have htop : (r : ℝ) ≤ (1+xi)*(p : ℝ) := by
    calc
      _ ≤ (1+theta)*R := hrm.2.2
      _ ≤ (1+xi)*R := mul_le_mul_of_nonneg_right (by linarith) hR.le
      _ ≤ (1+xi)*(p : ℝ) := mul_le_mul_of_nonneg_left hpm.2.1.le (by linarith)
  have hh : (1 : ℝ)/(p : ℝ) ≤ (1+xi)/(r : ℝ) :=
    (div_le_div_iff₀ hp0 hr0).mpr (by simpa only [one_mul] using htop)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hh

end ErdosInverseCells

end

section

namespace ErdosInversePrimeBin
open _root_.Filter ErdosInverseAlignment
open scoped Topology

theorem uniform_source_prime_bin_list {eta α C c : ℝ}
    (heta : 0 < eta) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R xi Sq Z : ℝ,∀ a : ℕ → ℤ,
      z^α ≤ R → eta ≤ xi → xi ≤ 1 → 0 ≤ Sq → 2*Sq*R^2*Z^20 ≤ z^C →
      (sourceRationalList (primeBin R xi) a Sq R Z c).card ≤ ⌈2/c^2⌉₊ := by
  let N : ℕ := ⌈max 1 (2*(C/α)/c^2)⌉₊
  have hN : max 1 (2*(C/α)/c^2) ≤ (N : ℝ) := Nat.le_ceil _
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_prime_bin_many heta N)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hα).eventually (eventually_ge_atTop R₀)] with z hz hlarge
  refine ⟨hz,?_⟩
  intro R xi Sq Z a hR hxi hxi1 hSq hheight
  have hbin := hR₀ R (hlarge.trans hR)
  have hR0 : 0 ≤ R := by linarith [hbin.1]
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hmany : N ≤ (primeBin R xi).card := hbin.2 xi hxi hxi1
  have hmanyR : (N : ℝ) ≤ ((primeBin R xi).card : ℝ) := by exact_mod_cast hmany
  have hPpos : 0 < (primeBin R xi).card := by
    have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hN
    have hpositive : (0 : ℝ) < (primeBin R xi).card := by linarith only [hN1,hmanyR]
    exact_mod_cast hpositive
  have henough : 2*(C/α) ≤ c^2*((primeBin R xi).card : ℝ) := by
    have hneed : 2*(C/α)/c^2 ≤ ((primeBin R xi).card : ℝ) :=
      (le_max_right _ _).trans (hN.trans hmanyR)
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hc)).mp hneed
  apply source_rational_list_bound (primeBin R xi) a hSq hR0 hz hα hC hc
  · intro p hp
    exact ((mem_primeBin hR0 hxi0 p).mp hp).1
  · intro p hp
    exact hR.trans ((mem_primeBin hR0 hxi0 p).mp hp).2.1.le
  · exact hheight
  · exact hPpos
  · exact henough

end ErdosInversePrimeBin

end

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

theorem logWidth_ge_half {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (hspan : Real.log (1+xi) ≤ Real.log (z/w)) :
    Real.log (1+xi)/2 ≤ logWidth w z xi := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.ceil_lt_add_one (div_pos (span_log_pos hw hwz) hlog).le
  have hm := mul_lt_mul_of_pos_right hc hlog
  have he : (Real.log (z/w)/Real.log (1+xi)+1)*Real.log (1+xi) =
      Real.log (z/w)+Real.log (1+xi) := by field_simp [hlog.ne']
  rw [he] at hm
  apply (le_div_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  change _ ≤ Real.log (z/w)
  change (binCount w z xi:ℝ)*Real.log (1+xi) < _ at hm
  nlinarith

theorem effectiveWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < effectiveWidth w z xi := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (logWidth_pos hw hwz hxi))

theorem effectiveWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    effectiveWidth w z xi ≤ xi := by
  have he := Real.exp_le_exp.mpr (logWidth_le hw hwz hxi)
  rw [Real.exp_log (by linarith : 0 < 1+xi)] at he
  exact sub_le_iff_le_add.mpr (by linarith)

theorem effectiveWidth_ge_quarter {w z xi : ℝ} (hw : 0 < w) (hwz : w < z)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hspan : Real.log (1+xi) ≤ Real.log (z/w)) :
    xi/4 ≤ effectiveWidth w z xi := by
  have hpos : 0 < 1+xi := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1-(1+xi)⁻¹ = xi/(1+xi) := by field_simp [hpos.ne'] <;> ring
  rw [he] at hl
  have hf : xi/2 ≤ xi/(1+xi) := div_le_div_of_nonneg_left hxi.le hpos (by linarith)
  have hwide := logWidth_ge_half hw hwz hxi hspan
  have hexp := Real.add_one_le_exp (logWidth w z xi)
  unfold effectiveWidth
  linarith

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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoxInflation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem bin_inflation_le_power {B C xi : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (1+xi)^(C*Real.log B) ≤ B^C := by
  have hB0 : 0 < B := by linarith
  have hx0 : 0 < 1+xi := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlx : Real.log (1+xi) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  rw [Real.rpow_def_of_pos hx0,Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlx (mul_nonneg hC hlB)]

theorem uniform_bin_inflation (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ B xi : ℝ,
      1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      (1+xi)^(C*Real.log B) ≤ z^((1:ℝ)/10) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1/10)).bound zero_lt_one
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hpow
  refine ⟨hz,?_⟩
  intro B xi hB hBz hxi0 hxi1
  have hz0 : 0 ≤ z := by linarith
  have hL0 : 0 ≤ Real.log z := Real.log_nonneg hz.le
  have hbound : (Real.log z)^C ≤ z^((1:ℝ)/10) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0 C),
      abs_of_nonneg (Real.rpow_nonneg hz0 ((1:ℝ)/10)),one_mul] using hpow
  exact (bin_inflation_le_power hB hC hxi0 hxi1).trans
    ((Real.rpow_le_rpow (by linarith : 0 ≤ B) hBz hC).trans hbound)

theorem sourceZ_le_small_power : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < sourceZ z ∧ sourceZ z ≤ z^((1:ℝ)/100) := by
  have hlog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 100
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hL
  dsimp only [Function.comp_apply] at hL
  refine ⟨hz,Real.exp_pos _,?_⟩
  have hz0 : 0 < z := by linarith
  have hlog0 : 0 ≤ Real.log z := (Real.log_pos hz).le
  rw [sourceZ,Real.rpow_def_of_pos hz0]
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left hlog0 (by norm_num : (0:ℝ)<100) hL
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ErdosInverseBoxHeight

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

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem source_B_bounds : ∀ᶠ z : ℝ in atTop,
    Real.exp 1 ≤ sourceW z ∧ 1 ≤ sourceB z ∧ sourceB z ≤ Real.log z := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound (Real.exp_pos (-1))
  have hl := Real.tendsto_log_atTop.eventually hsmall
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hl,hlarge] with z hz hL
  let L := Real.log z
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hL
  have hLL : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  have hsq0 : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq1 : 1 ≤ (Real.log L)^2 := by nlinarith
  have hbound : (Real.log L)^2 ≤ Real.exp (-1)*L := by
    change ‖(Real.log L)^(2:ℝ)‖ ≤ Real.exp (-1)*‖L^(1:ℝ)‖ at hz
    simpa only [Real.norm_eq_abs,Real.rpow_two,Real.rpow_one,
      abs_of_nonneg (sq_nonneg (Real.log L)),abs_of_pos hL0] using hz
  have hW : Real.exp 1 ≤ sourceW z := by
    apply (le_div_iff₀ hsq0).mpr
    have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le
    have he : Real.exp 1*Real.exp (-1)=1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hW0 : 0 < sourceW z := (Real.exp_pos 1).trans_le hW
  have hlogW : 1 ≤ Real.log (sourceW z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hW
    simpa only [Real.log_exp] using h
  have hWle : sourceW z ≤ L := div_le_self hL0.le hsq1
  have hlogle : Real.log (sourceW z) ≤ L := by
    have h := Real.log_le_log hW0 hWle
    have h' := Real.log_le_sub_one_of_pos hL0
    linarith
  refine ⟨hW,?_,?_⟩
  · exact (one_le_div (by linarith : 0 < Real.log (sourceW z))).mpr hlogle
  · exact div_le_self hL0.le hlogW

theorem sourceY_le_square {z : ℝ} (hL : 1 ≤ Real.log z) : (sourceY z : ℝ) ≤ z^2 := by
  have hden : 1 ≤ (Real.log z)^2 := by nlinarith
  exact (Nat.floor_le (div_nonneg (sq_nonneg z) (sq_nonneg _))).trans
    (div_le_self (sq_nonneg z) hden)

theorem source_cofactor_le_square {z p q : ℝ} (hL : 1 ≤ Real.log z)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hpq : p*q ≤ (sourceY z : ℝ)) : q ≤ z^2 := by
  have hmul : q ≤ p*q := by nlinarith [mul_le_mul_of_nonneg_right hp hq]
  exact hmul.trans (hpq.trans (sourceY_le_square hL))

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ClosedEulerIndividualUpper
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseEuler
open NumberTheoryLean ErdosPrimeInputs.MertensStrong

theorem cutoffPrimes_eq_filtered_Ioc (z : ℕ) :
    LargePrimeDeletion.cutoffPrimes z = (Finset.Ioc 0 z).filter Nat.Prime := by
  ext p
  rw [LargePrimeDeletion.mem_cutoffPrimes]
  simp only [Finset.mem_filter,Finset.mem_Ioc]
  exact ⟨fun h => ⟨⟨h.1.pos,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩

open _root_.Filter
open scoped Topology

end ErdosInverseEuler

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SmallModelSourceScales
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseEuler
open NumberTheoryLean

theorem log_smallModulus_eq_theta (w : ℝ) : Real.log (smallModulus w : ℝ) = Chebyshev.theta w := by
  have hn : ∀ p ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,(p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1.ne_zero
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  rw [Nat.cast_prod,Real.log_prod hn,cutoffPrimes_eq_filtered_Ioc]
  rfl

theorem log_smallModulus_le (w : ℝ) (hw : 0 ≤ w) :
    Real.log (smallModulus w : ℝ) ≤ Real.log 4*w := by
  rw [log_smallModulus_eq_theta]
  exact Chebyshev.theta_le_log4_mul_x hw

theorem smallModulus_le_exp (w : ℝ) (hw : 0 ≤ w) :
    (smallModulus w : ℝ) ≤ Real.exp (Real.log 4*w) := by
  have hp : (0 : ℝ) < smallModulus w := by exact_mod_cast smallModulus_pos w
  calc
    (smallModulus w : ℝ) = Real.exp (Real.log (smallModulus w : ℝ)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_smallModulus_le w hw)

end ErdosInverseEuler

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem sourceW_tendsto_atTop : Tendsto sourceW atTop atTop := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  have hlow : (fun z : ℝ => (Real.log z)^((1 : ℝ)/2)) ≤ᶠ[atTop] sourceW := by
    filter_upwards [Real.tendsto_log_atTop.eventually hs,
      Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hz hL
    have hL0 : 0 < Real.log z := by linarith
    have hLL : 0 < Real.log (Real.log z) := Real.log_pos hL
    have hh : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
      simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
        abs_of_nonneg (Real.rpow_nonneg hL0.le ((1 : ℝ)/2)),one_mul] using hz
    have hp : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
      rw [← Real.rpow_add hL0]
      norm_num
    apply (le_div_iff₀ (sq_pos_of_pos hLL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL0.le ((1 : ℝ)/2))]
  exact tendsto_atTop_mono' atTop hlow ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp Real.tendsto_log_atTop)

theorem smallModulus_source_power (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (smallModulus (sourceW z) : ℝ)^k ≤ (sourceZ z)^eps := by
  have hh := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (max 1 ((k : ℝ)*Real.log 4/eps))
  filter_upwards [hh,Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hLL hL
  have hL0 : 0 < Real.log z := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log z) := (le_max_left _ _).trans hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hW0 : 0 ≤ sourceW z := div_nonneg hL0.le (sq_nonneg _)
  have hpay : (k : ℝ)*Real.log 4 ≤ Real.log (Real.log z)*eps :=
    (div_le_iff₀ heps).mp ((le_max_right _ _).trans hLL)
  have hscale : (k : ℝ)*(Real.log 4*sourceW z) ≤ (Real.log z/Real.log (Real.log z))*eps := by
    calc
      _ = ((k : ℝ)*Real.log 4*Real.log z)/(Real.log (Real.log z))^2 := by unfold sourceW;ring
      _ ≤ (Real.log (Real.log z)*eps*Real.log z)/(Real.log (Real.log z))^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpay hL0.le) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ (Real.exp (Real.log 4*sourceW z))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (smallModulus_le_exp _ hW0) k
    _ = Real.exp ((k : ℝ)*(Real.log 4*sourceW z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((Real.log z/Real.log (Real.log z))*eps) := Real.exp_le_exp.mpr hscale
    _ = (sourceZ z)^eps := Real.exp_mul _ _

end ErdosInverseEuler

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem exp_loglog_sq_le_sourceZ (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,
      Real.exp (C*(Real.log (Real.log z))^2) ≤ (sourceZ z)^eps := by
  have hC1 : 0 < C+1 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) zero_lt_one).bound
    (div_pos heps hC1)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL0 : 0 < Real.log (Real.log z) := by change 1 ≤ Real.log (Real.log z) at hLL;linarith
  have hL0 : 0 < Real.log z := by linarith
  have hcube : (Real.log (Real.log z))^3 ≤ (eps/(C+1))*Real.log z := by
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,Real.rpow_one,
      abs_of_nonneg (pow_nonneg hLL0.le 3),abs_of_nonneg hL0.le] using hz
  have hpay : C*(Real.log (Real.log z))^3 ≤ eps*Real.log z := by
    have hm := (le_div_iff₀ hC1).mp (show (Real.log (Real.log z))^3 ≤ (eps*Real.log z)/(C+1) by
      simpa only [div_mul_eq_mul_div] using hcube)
    nlinarith [pow_nonneg hLL0.le 3]
  rw [sourceZ,← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLL0).mpr
  nlinarith only [hpay]

theorem log_pow_le_sourceZ (r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (Real.log z)^r ≤ (sourceZ z)^eps := by
  filter_upwards [exp_loglog_sq_le_sourceZ r eps (Nat.cast_nonneg _) heps,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hL0 : 0 < Real.log z := by linarith
  calc
    (Real.log z)^r = (Real.exp (Real.log (Real.log z)))^r := by rw [Real.exp_log hL0]
    _ = Real.exp ((r : ℝ)*Real.log (Real.log z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((r : ℝ)*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    _ ≤ _ := hz

theorem sourceZ_tendsto_atTop : Tendsto sourceZ atTop atTop := by
  have hlow : (fun z : ℝ => Real.log z) ≤ᶠ[atTop] sourceZ := by
    filter_upwards [log_pow_le_sourceZ 1 1 zero_lt_one] with z hz
    simpa only [pow_one,Real.rpow_one] using hz
  exact tendsto_atTop_mono' atTop hlow Real.tendsto_log_atTop

theorem smallModulus_mul_log_power (k r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,
      (smallModulus (sourceW z) : ℝ)^k*(Real.log z)^r ≤ (sourceZ z)^eps := by
  filter_upwards [smallModulus_source_power k (eps/2) (by positivity),
    log_pow_le_sourceZ r (eps/2) (by positivity),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with z hk hr hL
  calc
    _ ≤ (sourceZ z)^(eps/2)*(sourceZ z)^(eps/2) :=
      mul_le_mul hk hr (pow_nonneg hL _) (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = (sourceZ z)^(eps/2+eps/2) := (Real.rpow_add (Real.exp_pos _) _ _).symm
    _ = _ := by congr 1;ring

end ErdosInverseEuler

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceSamplePopulation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampling

theorem normalized_falling_eq_product (n h : ℕ) (hh : h ≤ n) (hn : 0 < n) :
    (n.descFactorial h : ℝ)/(n : ℝ)^h = ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ)) := by
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hden : (n : ℝ)^h = ∏ _i ∈ Finset.range h,(n : ℝ) := by simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hden,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i ≤ n := (Finset.mem_range.mp hi).le.trans hh
  rw [Nat.cast_sub hin]
  field_simp

theorem normalized_falling_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial h : ℝ)/(n : ℝ)^h) atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ))) atTop (𝓝 1) := by
    have hh := tendsto_finsetProd (Finset.range h) (fun i _ =>
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (hcast.const_div_atTop (i : ℝ)))
    simpa only [sub_zero,Finset.prod_const_one] using hh
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop h,eventually_ge_atTop (1 : ℕ)] with n hhn hn
  exact (normalized_falling_eq_product n h hhn (by omega)).symm

theorem sampling_prefactor_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^h/(n.descFactorial h : ℝ)) atTop (𝓝 1) := by
  have hh := (normalized_falling_tendsto h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div,inv_one] using hh

theorem sampling_prefactor_eventually_le_two (h : ℕ) :
    ∀ᶠ n : ℕ in atTop,(n : ℝ)^h/(n.descFactorial h : ℝ) ≤ 2 := by
  have hh := (tendsto_order.mp (sampling_prefactor_tendsto h)).2 2 (by norm_num)
  exact hh.mono (fun _ hn => hn.le)

end ErdosInverseSampling

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseSampling ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_sample_population (xi beta : ℝ) (h : ℕ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,sourceW z ≤ U → xi/4 ≤ theta → theta ≤ xi →
      0 < (primeBin U theta).card ∧ h ≤ (primeBin U theta).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U theta).card : ℝ) ∧
      ((primeBin U theta).card : ℝ)^h/((primeBin U theta).card.descFactorial h : ℝ) ≤ 2 := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (sampling_prefactor_eventually_le_two h)
  let M : ℕ := n0+h+⌈4*(h : ℝ)/beta⌉₊+1
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp (uniform_prime_bin_many (by positivity : 0 < xi/4) M)
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop U0] with z hz
  intro U theta hWU htlow hthigh
  have hmany := (hU0 U (hz.trans hWU)).2 theta htlow (hthigh.trans hxi1)
  have hM0 : n0 ≤ M := by dsimp [M];omega
  have hMh : h ≤ M := by dsimp [M];omega
  have hM1 : 1 ≤ M := by dsimp [M];omega
  have hMc : ⌈4*(h : ℝ)/beta⌉₊ ≤ M := by dsimp [M];omega
  refine ⟨by omega,hMh.trans hmany,?_,hn0 _ (hM0.trans hmany)⟩
  exact (Nat.le_ceil (4*(h : ℝ)/beta)).trans (by exact_mod_cast hMc.trans hmany)

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HarmonicConditioning
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem harmonicMass_nonneg (Q : Finset ℕ) : 0 ≤ harmonicMass Q := by unfold harmonicMass;positivity

theorem harmonicMass_pos (Q : Finset ℕ) (hQ : Q.Nonempty) (hp : ∀ q ∈ Q,0 < q) : 0 < harmonicMass Q := by
  apply Finset.sum_pos
  · intro q hq
    exact inv_pos.mpr (by exact_mod_cast hp q hq)
  · exact hQ

theorem tripleWeight_nonneg (x : (ℕ × ℕ) × ℕ) : 0 ≤ tripleWeight x := by unfold tripleWeight;positivity

theorem triple_weight_sum (P Q U : Finset ℕ) :
    (∑ x ∈ tripleSpace P Q U,tripleWeight x) = harmonicMass P*harmonicMass Q*harmonicMass U := by
  simp only [tripleSpace,Finset.sum_product,tripleWeight,harmonicMass,mul_assoc,← Finset.mul_sum,← Finset.sum_mul]

theorem cofactorReward_nonneg (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) :
    0 ≤ cofactorReward P U witness q := by unfold cofactorReward;positivity

theorem cofactorReward_upper (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) :
    cofactorReward P U witness q ≤ harmonicMass P*harmonicMass U := by
  calc
    _ ≤ ∑ p ∈ P,∑ u ∈ U,(p : ℝ)⁻¹*(u : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact le_rfl
      · positivity
    _ = _ := by simp only [harmonicMass,← Finset.mul_sum,← Finset.sum_mul]

theorem conditionalReward_bounds (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ)
    (hDen : 0 < harmonicMass P*harmonicMass U) : 0 ≤ conditionalReward P U witness q ∧ conditionalReward P U witness q ≤ 1 := by
  refine ⟨div_nonneg (cofactorReward_nonneg P U witness q) hDen.le,?_⟩
  exact (div_le_iff₀ hDen).mpr (by simpa only [one_mul] using cofactorReward_upper P U witness q)

theorem weightedWitness_decomposition (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U witness = ∑ q ∈ Q,(q : ℝ)⁻¹*cofactorReward P U witness q := by
  unfold weightedWitness witnessPairs
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,tripleWeight]
  have he : ∀ p q u : ℕ,(if witness (p,q) u then (p : ℝ)⁻¹*(q : ℝ)⁻¹*(u : ℝ)⁻¹ else 0) =
      (q : ℝ)⁻¹*(if witness (p,q) u then (p : ℝ)⁻¹*(u : ℝ)⁻¹ else 0) := by
    intro p q u
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [cofactorReward,Finset.mul_sum]

end ErdosInverseCells

end

section

namespace ErdosInverseCells

theorem weightedWitness_conditioning (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U witness/(harmonicMass P*harmonicMass U) =
      ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q := by
  rw [weightedWitness_decomposition,Finset.sum_div]
  simp only [conditionalReward,mul_div_assoc]

theorem conditioned_reward_upper (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (hDen : 0 < harmonicMass P*harmonicMass U) (q : ℕ) :
    (q : ℝ)⁻¹*conditionalReward P U witness q ≤ (q : ℝ)⁻¹ := by
  have hh := mul_le_mul_of_nonneg_left (conditionalReward_bounds P U witness q hDen).2
    (inv_nonneg.mpr (Nat.cast_nonneg q))
  simpa only [mul_one] using hh

theorem condition_harmonic_density (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hDen : 0 < harmonicMass P*harmonicMass U)
    (hBad : sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness) :
    sigma*(∑ q ∈ Q,(q : ℝ)⁻¹) < ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q := by
  rw [← weightedWitness_conditioning]
  apply (lt_div_iff₀ hDen).mpr
  have he : (sigma*(∑ q ∈ Q,(q : ℝ)⁻¹))*(harmonicMass P*harmonicMass U) =
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by unfold harmonicMass;ring
  rwa [he]

theorem uncondition_harmonic_density (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hDen : 0 < harmonicMass P*harmonicMass U)
    (hBad : sigma*(∑ q ∈ Q,(q : ℝ)⁻¹) < ∑ q ∈ Q,(q : ℝ)⁻¹*conditionalReward P U witness q) :
    sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness := by
  rw [← weightedWitness_conditioning] at hBad
  have hh := (lt_div_iff₀ hDen).mp hBad
  have he : (sigma*(∑ q ∈ Q,(q : ℝ)⁻¹))*(harmonicMass P*harmonicMass U) =
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by unfold harmonicMass;ring
  rwa [he] at hh

end ErdosInverseCells

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

theorem selectionProduct_primeFactors {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) :
    (selectionProduct f).primeFactors = selectionPrimes f := by
  rw [selectionProduct_eq_union P hd f hf]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨i, _hi, hpi⟩ := Finset.mem_biUnion.mp hp
  exact hP i p (hf i hpi)

theorem selectionProduct_pos {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) : 0 < selectionProduct f :=
  Finset.prod_pos (fun i _ => Finset.prod_pos (fun p hp => (hP i p (hf i hp)).pos))

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem selectionProduct_injOn {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Set.InjOn selectionProduct (selections P m : Set (ι → Finset ℕ)) := by
  intro f hf g hg he
  have hfs := (mem_selections P m f).mp hf
  have hgs := (mem_selections P m g).mp hg
  have hu : selectionPrimes f = selectionPrimes g := by
    rw [← selectionProduct_primeFactors P hP hd f (fun i => (hfs i).1),
      ← selectionProduct_primeFactors P hP hd g (fun i => (hgs i).1), he]
  funext i
  rw [← recover_bin P hd f (fun j => (hfs j).1) i,
    ← recover_bin P hd g (fun j => (hgs j).1) i, hu]

theorem selections_card {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) :
    (selections P m).card = ∏ i, (P i).card.choose (m i) := by
  simp only [selections, Fintype.card_piFinset, Finset.card_powersetCard]

theorem cofactorChoices_card {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (cofactorChoices P m).card = ∏ i, (P i).card.choose (m i) := by
  rw [cofactorChoices, Finset.card_image_of_injOn (selectionProduct_injOn P m hP hd)]
  exact selections_card P m

theorem cofactor_positive {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p) (q : ℕ)
    (hq : q ∈ cofactorChoices P m) : 0 < q := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact selectionProduct_pos P hP f (fun i => ((mem_selections P m f).mp hf i).1)

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices

theorem half_power_le_choose (n m : ℕ) (hm : 2*m ≤ n) :
    ((n : ℝ)/2)^m/(m.factorial : ℝ) ≤ (n.choose m : ℝ) := by
  have hsub : m ≤ n+1 := by omega
  have hhalf : (n : ℝ)/2 ≤ ((n+1-m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hh : 2*(m : ℝ) ≤ n := by exact_mod_cast hm
    linarith
  calc
    _ ≤ (((n+1-m : ℕ) : ℝ)^m)/(m.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf m) (Nat.cast_nonneg _)
    _ ≤ (n.choose m : ℝ) := by
      simpa only [Nat.cast_pow] using (Nat.pow_le_choose (α := ℝ) m n)

theorem factorial_le_uniform_power (m K : ℕ) (hm : m ≤ K) :
    (m.factorial : ℝ) ≤ (K : ℝ)^m := by
  exact_mod_cast (Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left hm m)

theorem scaled_power_le_choose (n m K : ℕ) (hK : 0 < K) (hm : m ≤ K)
    (hn : 2*m ≤ n) (R H : ℝ) (hR : 0 ≤ R) (hH : 0 < H)
    (hcount : R/H ≤ n) :
    (R/(2*H*(K : ℝ)))^m ≤ (n.choose m : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hp : (R/H/2)^m ≤ ((n : ℝ)/2)^m :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hcount (by norm_num)) m
  calc
    _ = (R/H/2)^m/(K : ℝ)^m := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ ((n : ℝ)/2)^m/(K : ℝ)^m :=
      div_le_div_of_nonneg_right hp (pow_nonneg hKR.le _)
    _ ≤ ((n : ℝ)/2)^m/(m.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfact (factorial_le_uniform_power m K hm)
    _ ≤ (n.choose m : ℝ) := half_power_le_choose n m hn

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem selectionProduct_squarefree {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : ∀ i, f i ⊆ P i) : Squarefree (selectionProduct f) := by
  rw [selectionProduct_eq_union P hd f hf]
  have hp (p : ℕ) (h : p ∈ selectionPrimes f) : p.Prime := by
    obtain ⟨i, _hi, hpi⟩ := Finset.mem_biUnion.mp h
    exact hP i p (hf i hpi)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hpp q hqq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hpp) (hp q hqq)).mpr hpq)
  · intro p hpp
    exact (hp p hpp).squarefree

theorem cofactor_squarefree {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (q : ℕ) (hq : q ∈ cofactorChoices P m) : Squarefree q := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact selectionProduct_squarefree P hP hd f (fun i => ((mem_selections P m f).mp hf i).1)

theorem prime_factor_bin_recovery {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ι → Finset ℕ) (hf : f ∈ selections P m) (i : ι) :
    (selectionProduct f).primeFactors ∩ P i = f i := by
  have hs := (mem_selections P m f).mp hf
  rw [selectionProduct_primeFactors P hP hd f (fun j => (hs j).1)]
  exact recover_bin P hd f (fun j => (hs j).1) i

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem cofactor_card_scaled_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, 2*m i ≤ (P i).card)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (H : ℝ) (hH : 0 < H)
    (hcount : ∀ i, R i/H ≤ (P i).card) :
    (∏ i, (R i)^(m i))/(2*H*((∑ i, m i)+1 : ℕ))^(∑ i, m i) ≤
      ((cofactorChoices P m).card : ℝ) := by
  let K : ℕ := (∑ i, m i)+1
  have hK : 0 < K := Nat.succ_pos _
  have hmi (i : ι) : m i ≤ K := by
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans
      (Nat.le_succ _)
  calc
    _ = ∏ i, (R i/(2*H*(K : ℝ)))^(m i) := by
      simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rfl
    _ ≤ ∏ i, ((P i).card.choose (m i) : ℝ) :=
      Finset.prod_le_prod (fun i _ => pow_nonneg (div_nonneg (hR i) (by positivity)) _)
        (fun i _ => scaled_power_le_choose (P i).card (m i) K hK (hmi i)
          (hm i) (R i) H (hR i) hH (hcount i))
    _ = ((cofactorChoices P m).card : ℝ) := by
      rw [cofactorChoices_card P m hP hd, Nat.cast_prod]

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices

theorem denominator_loss_budget (A C T : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hT : 1 ≤ T) (k : ℕ) (hk : (k : ℝ) ≤ C*T) :
    (2*(A*Real.exp T)*((k+1 : ℕ) : ℝ))^k ≤
      Real.exp (C*(2*A+C+1)*T^2) := by
  have hT0 : 0 ≤ T := by linarith
  have hD : 0 ≤ 2*A+C+1 := by positivity
  have hconst : 2*A ≤ Real.exp (2*A*T) := by
    have he := Real.add_one_le_exp (2*A)
    have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2*A))
    norm_num only [mul_one] at hm
    linarith
  have hkexp : ((k+1 : ℕ) : ℝ) ≤ Real.exp (C*T) := by
    have he := Real.add_one_le_exp (C*T)
    push_cast
    linarith
  have hbase : 2*(A*Real.exp T)*((k+1 : ℕ) : ℝ) ≤
      Real.exp ((2*A+C+1)*T) := by
    calc
      _ = (2*A)*Real.exp T*((k+1 : ℕ) : ℝ) := by ring
      _ ≤ Real.exp (2*A*T)*Real.exp T*Real.exp (C*T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le) hkexp
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  calc
    _ ≤ (Real.exp ((2*A+C+1)*T))^k := pow_le_pow_left₀ (by positivity) hbase k
    _ = Real.exp ((k : ℝ)*((2*A+C+1)*T)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (C*(2*A+C+1)*T^2) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hk (mul_nonneg hD hT0)
      nlinarith only [h]

theorem cofactor_card_exponential_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ)
    (hP : ∀ i, ∀ p ∈ P i, Nat.Prime p)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hm : ∀ i, 2*m i ≤ (P i).card)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (A C T : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hcount : ∀ i, R i/(A*Real.exp T) ≤ (P i).card)
    (hk : ((∑ i, m i) : ℝ) ≤ C*T) :
    (∏ i, (R i)^(m i))*Real.exp (-C*(2*A+C+1)*T^2) ≤
      ((cofactorChoices P m).card : ℝ) := by
  have hden := denominator_loss_budget A C T hA hC hT (∑ i, m i)
    (by simpa only [Nat.cast_sum] using hk)
  have hfinite := cofactor_card_scaled_lower P m hP hd hm R hR (A*Real.exp T) (by positivity) hcount
  calc
    _ = (∏ i, (R i)^(m i))/Real.exp (C*(2*A+C+1)*T^2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ (∏ i, (R i)^(m i))/(2*(A*Real.exp T)*((∑ i, m i)+1 : ℕ))^(∑ i, m i) :=
      div_le_div_of_nonneg_left (Finset.prod_nonneg (fun i _ => pow_nonneg (hR i) _))
        (by positivity) hden
    _ ≤ _ := hfinite

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin

theorem source_log_budget : ∀ᶠ z : ℝ in atTop,
    0 < Real.log z ∧ 1 ≤ Real.log (Real.log z) ∧
    0 < sourceW z ∧ 0 < sourceB z ∧
    Real.log (sourceB z) ≤ Real.log (Real.log z) := by
  filter_upwards [source_B_bounds,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with z hs ht
  have hw : 0 < sourceW z := (Real.exp_pos 1).trans_le hs.1
  have hb : 0 < sourceB z := by linarith [hs.2.1]
  exact ⟨hb.trans_le hs.2.2, ht, hw, hb, Real.log_le_log hb hs.2.2⟩

theorem sqrt_sourceW_dominates (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ z : ℝ in atTop, D*Real.log (Real.log z) ≤ Real.sqrt (sourceW z) := by
  have heps : 0 < 1/(D+1) := by positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).bound heps
  filter_upwards [Real.tendsto_log_atTop.eventually hsmall, source_log_budget] with z hz hs
  have hT : 0 < Real.log (Real.log z) := by linarith [hs.2.1]
  have hbound : (Real.log (Real.log z))^2 ≤ Real.sqrt (Real.log z)/(D+1) := by
    have hh : (Real.log (Real.log z))^2 ≤ (1/(D+1))*(Real.log z)^((1 : ℝ)/2) := by
      simpa only [Real.norm_eq_abs, Real.rpow_two,
        abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
        abs_of_nonneg (Real.rpow_nonneg hs.1.le ((1 : ℝ)/2))] using hz
    rw [← Real.sqrt_eq_rpow] at hh
    simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using hh
  have hpay : D*(Real.log (Real.log z))^2 ≤ Real.sqrt (Real.log z) := by
    have hh := (le_div_iff₀ (by positivity : 0 < D+1)).mp hbound
    nlinarith [sq_nonneg (Real.log (Real.log z))]
  have he : Real.sqrt (sourceW z) = Real.sqrt (Real.log z)/Real.log (Real.log z) := by
    rw [sourceW, Real.sqrt_div hs.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hT]
  rw [he]
  apply (le_div_iff₀ hT).mpr
  nlinarith only [hpay]

theorem source_multiplicity_room (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop,
      2*C*Real.log (sourceB z) ≤ eta*Real.sqrt (sourceW z)/8 := by
  filter_upwards [sqrt_sourceW_dominates (16*C/eta) (by positivity), source_log_budget]
    with z hh hs
  have hdiv : (16*C*Real.log (Real.log z))/eta ≤ Real.sqrt (sourceW z) := by
    simpa only [div_mul_eq_mul_div] using hh
  have hmul := (div_le_iff₀ heta).mp hdiv
  have hlog := mul_le_mul_of_nonneg_left hs.2.2.2.2 (show 0 ≤ 2*C by positivity)
  linarith

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin

theorem source_prime_bin_data (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, ∀ R xi : ℝ, sourceW z ≤ R → eta ≤ xi → xi ≤ 1 →
      (1+xi)*R ≤ z →
      2*C*Real.log (sourceB z) ≤ ((primeBin R xi).card : ℝ) ∧
      ((1+xi)*R)/((8/eta)*Real.log z) ≤ ((primeBin R xi).card : ℝ) := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count heta)
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop R0,
    source_multiplicity_room eta C heta hC, source_log_budget] with z hz hroom hs
  have hL : 0 < Real.log z := hs.1
  intro R xi hR hxi hxi1 hRz
  have hc := hR0 R (hz.trans hR)
  have hRp : 0 < R := by linarith [hc.1]
  have hxp : 0 < xi := heta.trans_le hxi
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hc.1])
  have hU : R ≤ (1+xi)*R := by nlinarith
  have hlogle : Real.log R ≤ Real.log z := Real.log_le_log hRp (hU.trans hRz)
  have htwo : (1+xi)*R ≤ 2*R := by nlinarith
  have hlower := (hc.2 xi hxi hxi1).1
  constructor
  · calc
      _ ≤ eta*Real.sqrt (sourceW z)/8 := hroom
      _ ≤ eta*Real.sqrt R/8 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR) heta.le)
          (by norm_num)
      _ ≤ xi*R/(4*Real.log R) := bin_scale_sqrt_lower hc.1 heta hxi
      _ ≤ _ := hlower
  · calc
      _ = eta*((1+xi)*R)/(8*Real.log z) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ ≤ eta*(2*R)/(8*Real.log z) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htwo heta.le) (by positivity)
      _ = eta*R/(4*Real.log z) := by ring
      _ ≤ eta*R/(4*Real.log R) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hlogle (by norm_num))
      _ ≤ xi*R/(4*Real.log R) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxi hRp.le) (by positivity)
      _ ≤ _ := hlower

theorem source_cofactor_count_lower (eta C : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] (R xi : ι → ℝ) (m : ι → ℕ),
      (∀ i, sourceW z ≤ R i) → (∀ i, eta ≤ xi i) → (∀ i, xi i ≤ 1) →
      (∀ i, (1+xi i)*R i ≤ z) →
      Pairwise (fun i j => Disjoint (primeBin (R i) (xi i)) (primeBin (R j) (xi j))) →
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      (∏ i, ((1+xi i)*R i)^(m i))*
        Real.exp (-C*(16/eta+C+1)*(Real.log (Real.log z))^2) ≤
        ((cofactorChoices (fun i => primeBin (R i) (xi i)) m).card : ℝ) := by
  filter_upwards [source_prime_bin_data eta C heta hC, source_log_budget] with z hb hs
  intro ι inst R xi m hR hxi hxi1 hU hd hk
  have hprime (i : ι) (p : ℕ) (hp : p ∈ primeBin (R i) (xi i)) : Nat.Prime p :=
    ((mem_primeBin ((hs.2.2.1).trans_le (hR i)).le (heta.le.trans (hxi i)) p).mp hp).1
  have hhalf (i : ι) : 2*m i ≤ (primeBin (R i) (xi i)).card := by
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    have hmiR : (m i : ℝ) ≤ ((∑ j, m j : ℕ) : ℝ) := by exact_mod_cast hmi
    have hh := (hb (R i) (xi i) (hR i) (hxi i) (hxi1 i) (hU i)).1
    have hmR : 2*(m i : ℝ) ≤ (primeBin (R i) (xi i)).card := by linarith
    exact_mod_cast hmR
  have hcount (i : ι) : ((1+xi i)*R i)/((8/eta)*Real.exp (Real.log (Real.log z))) ≤
      ((primeBin (R i) (xi i)).card : ℝ) := by
    rw [Real.exp_log hs.1]
    exact (hb (R i) (xi i) (hR i) (hxi i) (hxi1 i) (hU i)).2
  have hsize : ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (Real.log z) :=
    hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
  have hnonneg (i : ι) : 0 ≤ (1+xi i)*R i :=
    mul_nonneg (by linarith [hxi i]) ((hs.2.2.1).trans_le (hR i)).le
  have hh := cofactor_card_exponential_lower (fun i => primeBin (R i) (xi i)) m
    hprime hd hhalf (fun i => (1+xi i)*R i) hnonneg (8/eta) C (Real.log (Real.log z))
    (by positivity) hC hs.2.1 hcount (by simpa only [Nat.cast_sum] using hsize)
  have he : (2 : ℝ)*(8/eta) = 16/eta := by ring
  rw [he] at hh
  exact hh

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
open NumberTheoryLean.LogarithmicBinPartition

theorem source_span_geometry : ∀ᶠ z : ℝ in atTop,
    0 < sourceW z ∧ sourceW z < z ∧
    ∀ xi : ℝ, 0 < xi → xi ≤ 1 → Real.log (1+xi) ≤ Real.log (z/sourceW z) := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [source_log_budget, hsmall, eventually_gt_atTop (1 : ℝ)] with z hs hz hz1
  have hzp : 0 < z := by linarith
  have hlogz : 0 < Real.log z := hs.1
  have hlog : Real.log z ≤ (1/2 : ℝ)*z := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogz, abs_of_pos hzp, id_eq] using hz
  have hden : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith [hs.2.1]
  have hWle : sourceW z ≤ Real.log z := div_le_self hlogz.le hden
  have hw : 0 < sourceW z := hs.2.2.1
  have hwz : sourceW z < z := by linarith
  refine ⟨hw, hwz, ?_⟩
  intro xi hxi hxi1
  apply Real.log_le_log (by linarith : 0 < 1+xi)
  apply (le_div_iff₀ hw).mpr
  nlinarith [mul_le_mul_of_nonneg_right hxi1 hw.le]

theorem cofactorScale_nonneg {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) : 0 ≤ cofactorScale z xi m := by
  apply Finset.prod_nonneg
  intro i _
  have hb := bin_source_bounds hw hwz hxi i
  exact pow_nonneg ((hw.trans_le hb.1).trans hb.2.1).le _

theorem actual_source_many_cofactors (C xi : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      cofactorScale z xi m*Real.exp (-C*(64/xi+C+1)*(Real.log (Real.log z))^2) ≤
        ((cofactorChoices (actualBins z xi) m).card : ℝ) := by
  filter_upwards [source_cofactor_count_lower (xi/4) C (by positivity) hC, source_span_geometry]
    with z hc hs
  intro m hm
  have hwide := effectiveWidth_ge_quarter hs.1 hs.2.1 hxi hxi1 (hs.2.2 xi hxi hxi1)
  have hwidth := effectiveWidth_le hs.1 hs.2.1 hxi
  have hh := hc (Fin (binCount (sourceW z) z xi)) (lower (sourceW z) z xi)
    (width (sourceW z) z xi) m
    (fun i => (bin_source_bounds hs.1 hs.2.1 hxi i).1)
    (fun _ => hwide) (fun _ => hwidth.trans hxi1)
    (fun i => (bin_source_bounds hs.1 hs.2.1 hxi i).2.2)
    (fun i j hij => bins_pairwise_disjoint hs.1 hs.2.1 hxi i j hij) hm
  have he : (16 : ℝ)/(xi/4) = 64/xi := by
    rw [div_div_eq_mul_div]
    norm_num
  rw [he] at hh
  exact hh

theorem actual_source_many_cofactors_power (C xi eps : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      cofactorScale z xi m/(sourceZ z)^eps ≤
        ((cofactorChoices (actualBins z xi) m).card : ℝ) := by
  have hD : 0 ≤ C*(64/xi+C+1) := by positivity
  filter_upwards [actual_source_many_cofactors C xi hC hxi hxi1,
    exp_loglog_sq_le_sourceZ (C*(64/xi+C+1)) eps hD heps, source_span_geometry]
    with z hc hg hs
  intro m hm
  calc
    _ ≤ cofactorScale z xi m/Real.exp ((C*(64/xi+C+1))*(Real.log (Real.log z))^2) :=
      div_le_div_of_nonneg_left (cofactorScale_nonneg hs.1 hs.2.1 hxi m) (Real.exp_pos _) hg
    _ = cofactorScale z xi m*Real.exp (-C*(64/xi+C+1)*(Real.log (Real.log z))^2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ _ := hc m hm

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq
open ErdosInverseBoxHeight ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem selectionProduct_upper {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) (hf : f ∈ selections P m)
    (U : ι → ℝ) (hU : ∀ i, ∀ p ∈ P i, (p : ℝ) ≤ U i) :
    (selectionProduct f : ℝ) ≤ ∏ i, (U i)^(m i) := by
  rw [selectionProduct, Nat.cast_prod]
  apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
  intro i _
  have hs := (mem_selections P m f).mp hf i
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _p ∈ f i, U i := Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
      (fun p hp => hU i p (hs.1 hp))
    _ = (U i)^(m i) := by rw [Finset.prod_const, hs.2]

theorem selectionProduct_lower {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (f : ι → Finset ℕ) (hf : f ∈ selections P m)
    (U : ι → ℝ) (hU : ∀ i, 0 ≤ U i) (F : ℝ) (hF : 0 < F)
    (hlower : ∀ i, ∀ p ∈ P i, U i/F ≤ (p : ℝ)) :
    (∏ i, (U i)^(m i))/F^(∑ i, m i) ≤ (selectionProduct f : ℝ) := by
  calc
    _ = ∏ i, (U i/F)^(m i) := by
      simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ (selectionProduct f : ℝ) := by
      rw [selectionProduct, Nat.cast_prod]
      apply Finset.prod_le_prod (fun i _ => pow_nonneg (div_nonneg (hU i) hF.le) _)
      intro i _
      have hs := (mem_selections P m f).mp hf i
      rw [Nat.cast_prod, ← hs.2, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => div_nonneg (hU i) hF.le)
        (fun p hp => hlower i p (hs.1 hp))

theorem actual_cofactor_range {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    cofactorScale z xi m/(1+xi)^(∑ i, m i) ≤ (q : ℝ) ∧ (q : ℝ) ≤ cofactorScale z xi m := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  have hU (i : Fin (binCount (sourceW z) z xi)) : 0 ≤ upper (sourceW z) z xi i := by
    have hb := bin_source_bounds hw hwz hxi i
    exact ((hw.trans_le hb.1).trans hb.2.1).le
  have hlower (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
      upper (sourceW z) z xi i/(1+xi) ≤ (p : ℝ) := by
    have hb := (mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
    have hwidth := effectiveWidth_le hw hwz hxi
    have hl : upper (sourceW z) z xi i/(1+xi) ≤ lower (sourceW z) z xi i := by
      apply (div_le_iff₀ (by linarith : 0 < 1+xi)).mpr
      change (1+effectiveWidth (sourceW z) z xi)*lower (sourceW z) z xi i ≤ _
      have hl0 : 0 ≤ lower (sourceW z) z xi i := (endpoint_pos hw i.1).le
      have h := mul_le_mul_of_nonneg_right hwidth hl0
      nlinarith
    exact hl.trans hb.2.1.le
  have hupper (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
      (p : ℝ) ≤ upper (sourceW z) z xi i :=
    ((mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp).2.2
  exact ⟨selectionProduct_lower (actualBins z xi) m f hf (upper (sourceW z) z xi) hU (1+xi)
      (by linarith) hlower,
    selectionProduct_upper (actualBins z xi) m f hf (upper (sourceW z) z xi) hupper⟩

theorem actual_cofactor_positive {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) : 0 < q :=
  cofactor_positive (actualBins z xi) m
    (fun i _ hp => (bin_prime_in_source hw hwz hxi i hp).1) q hq

theorem actual_cofactor_ratio {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q r : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) (hr : r ∈ cofactorChoices (actualBins z xi) m) :
    (q : ℝ)/(r : ℝ) ≤ (1+xi)^(∑ i, m i) := by
  have hqp := actual_cofactor_range hw hwz hxi m q hq
  have hrp := actual_cofactor_range hw hwz hxi m r hr
  have hF : 0 < (1+xi)^(∑ i, m i) := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast actual_cofactor_positive hw hwz hxi m r hr
  apply (div_le_iff₀ hr0).mpr
  have h := (div_le_iff₀ hF).mp hrp.1
  simpa only [mul_comm] using hqp.2.trans h

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

theorem actual_reciprocal_variation {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q r : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) (hr : r ∈ cofactorChoices (actualBins z xi) m) :
    (q : ℝ)⁻¹ ≤ (1+xi)^(∑ i, m i)*(r : ℝ)⁻¹ := by
  have h := actual_cofactor_ratio hw hwz hxi m r q hr hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast actual_cofactor_positive hw hwz hxi m q hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast actual_cofactor_positive hw hwz hxi m r hr
  have hm := (div_le_iff₀ hq0).mp h
  have hi : (1 : ℝ)/(q : ℝ) ≤ (1+xi)^(∑ i, m i)/(r : ℝ) := by
    apply (div_le_div_iff₀ hq0 hr0).mpr
    simpa only [one_mul] using hm
  simpa only [one_div, div_eq_mul_inv, one_mul] using hi

theorem source_bin_factor_subpower (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ (xi : ℝ) (k : ℕ), 0 < xi → xi ≤ 1 →
      (k : ℝ) ≤ C*Real.log (sourceB z) → (1+xi)^k ≤ (sourceZ z)^eps := by
  filter_upwards [source_log_budget, exp_loglog_sq_le_sourceZ C eps hC heps] with z hs hg
  intro xi k hxi hxi1 hk
  have hbase : 0 < 1+xi := by linarith
  have hlog : Real.log (1+xi) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hbase
    linarith
  have hlen : (k : ℝ) ≤ C*Real.log (Real.log z) :=
    hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
  have hT : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith [hs.2.1]
  calc
    _ = Real.exp ((k : ℝ)*Real.log (1+xi)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    _ ≤ Real.exp (C*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (k : ℝ)*1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
        _ ≤ C*Real.log (Real.log z) := by simpa only [mul_one] using hlen
        _ ≤ _ := mul_le_mul_of_nonneg_left hT hC
    _ ≤ _ := hg

theorem source_cofactor_weight_variation (C xi eps : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i, m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) → ∀ q r : ℕ,
      q ∈ cofactorChoices (actualBins z xi) m → r ∈ cofactorChoices (actualBins z xi) m →
      (q : ℝ)/(r : ℝ) ≤ (sourceZ z)^eps ∧
        (q : ℝ)⁻¹ ≤ (sourceZ z)^eps*(r : ℝ)⁻¹ := by
  filter_upwards [source_span_geometry, source_bin_factor_subpower C eps hC heps] with z hs hb
  intro m hm q r hq hr
  have hf := hb xi (∑ i, m i) hxi hxi1 hm
  exact ⟨(actual_cofactor_ratio hs.1 hs.2.1 hxi m q r hq hr).trans hf,
    (actual_reciprocal_variation hs.1 hs.2.1 hxi m q r hq hr).trans
      (mul_le_mul_of_nonneg_right hf (inv_nonneg.mpr (Nat.cast_nonneg r)))⟩

end ErdosCofactorChoices

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints NumberTheoryLean.LogarithmicBinPartition

theorem actual_cofactorScale_pos {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) : 0 < cofactorScale z xi m := by
  apply Finset.prod_pos
  intro i _
  have hb := bin_source_bounds hw hwz hxi i
  exact pow_pos ((hw.trans_le hb.1).trans hb.2.1) _

theorem actual_cofactor_squarefree {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) : Squarefree q :=
  cofactor_squarefree (actualBins z xi) m (fun i _ hp => (bin_prime_in_source hw hwz hxi i hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) q hq

theorem actual_cofactor_effective_range {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    cofactorScale z xi m/(1+effectiveWidth (sourceW z) z xi)^(∑ i,m i) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ cofactorScale z xi m := by
  have hupper := (actual_cofactor_range hw hwz hxi m q hq).2
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have htheta := effectiveWidth_pos hw hwz hxi
  have hF : 0 < 1+effectiveWidth (sourceW z) z xi := by linarith
  have hU : ∀ i : Fin (binCount (sourceW z) z xi),0 ≤ upper (sourceW z) z xi i := by
    intro i
    have hb := bin_source_bounds hw hwz hxi i
    exact ((hw.trans_le hb.1).trans hb.2.1).le
  have hlower : ∀ i : Fin (binCount (sourceW z) z xi),∀ p ∈ actualBins z xi i,
      upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) ≤ (p : ℝ) := by
    intro i p hp
    have hh := (mem_primeBin (endpoint_pos hw i.1).le htheta.le p).mp hp
    have he : upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) = lower (sourceW z) z xi i := by
      change ((1+effectiveWidth (sourceW z) z xi)*lower (sourceW z) z xi i)/(1+effectiveWidth (sourceW z) z xi) = _
      field_simp
    rw [he]
    exact hh.2.1.le
  exact ⟨selectionProduct_lower (actualBins z xi) m f hf (upper (sourceW z) z xi) hU
    (1+effectiveWidth (sourceW z) z xi) hF hlower,hupper⟩

theorem source_cofactor_cell_data (C xi eps : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      0 < cofactorScale z xi m ∧ 0 < (cofactorChoices (actualBins z xi) m).card ∧
      cofactorScale z xi m/(sourceZ z)^eps ≤ ((cofactorChoices (actualBins z xi) m).card : ℝ) ∧
      ∀ q ∈ cofactorChoices (actualBins z xi) m,0 < q ∧ Squarefree q := by
  filter_upwards [source_span_geometry,actual_source_many_cofactors_power C xi eps hC hxi hxi1 heps] with z hs hc
  intro m hm
  have hS := actual_cofactorScale_pos hs.1 hs.2.1 hxi m
  have hcount := hc m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hn : (0 : ℝ) < (cofactorChoices (actualBins z xi) m).card :=
    (div_pos hS (Real.rpow_pos_of_pos hZ eps)).trans_le hcount
  refine ⟨hS,by exact_mod_cast hn,hcount,?_⟩
  intro q hq
  exact ⟨actual_cofactor_positive hs.1 hs.2.1 hxi m q hq,
    actual_cofactor_squarefree hs.1 hs.2.1 hxi m q hq⟩

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceLabelCount
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem mem_labelFiber {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) (q : ℕ) :
    q ∈ labelFiber Q label i ↔ q ∈ Q ∧ label q = i := Finset.mem_filter

theorem labelFiber_subset {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) :
    labelFiber Q label i ⊆ Q := Finset.filter_subset _ _

theorem label_fibers_partition {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) :
    Finset.univ.biUnion (labelFiber Q label) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hq
    exact labelFiber_subset Q label i hi
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨label q,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

theorem label_fibers_disjoint {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i j : ι) (hij : i ≠ j) :
    Disjoint (labelFiber Q label i) (labelFiber Q label j) := by
  apply Finset.disjoint_left.mpr
  intro q hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_label_fibers {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (f : ℕ → ℝ) :
    (∑ i : ι,∑ q ∈ labelFiber Q label i,f q) = ∑ q ∈ Q,f q := by
  calc
    _ = ∑ q ∈ Finset.univ.biUnion (labelFiber Q label),f q :=
      (Finset.sum_biUnion (fun i _ j _ hij => label_fibers_disjoint Q label i j hij)).symm
    _ = _ := by rw [label_fibers_partition]

theorem mem_discardedPoints {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (q : ℕ) :
    q ∈ discardedPoints Q label tau ↔ q ∈ Q ∧ ((labelFiber Q label (label q)).card : ℝ) < tau := by
  constructor
  · intro hq
    obtain ⟨i,hi,hqi⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqQ,he⟩ := Finset.mem_filter.mp hqi
    refine ⟨hqQ,?_⟩
    rw [he]
    exact (Finset.mem_filter.mp hi).2
  · rintro ⟨hq,hs⟩
    exact Finset.mem_biUnion.mpr ⟨label q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,
      Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

theorem discardedPoints_subset {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) :
    discardedPoints Q label tau ⊆ Q := fun q hq => (mem_discardedPoints Q label tau q).mp hq |>.1

theorem sum_small_fibers {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (f : ℕ → ℝ) :
    (∑ i ∈ smallLabels Q label tau,∑ q ∈ labelFiber Q label i,f q) = ∑ q ∈ discardedPoints Q label tau,f q :=
  (Finset.sum_biUnion (fun i _ j _ hij => label_fibers_disjoint Q label i j hij)).symm

theorem discardedPoints_card_bound {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι)
    (tau : ℝ) (htau : 0 ≤ tau) :
    ((discardedPoints Q label tau).card : ℝ) ≤ (Fintype.card ι : ℝ)*tau := by
  calc
    _ ≤ ∑ i ∈ smallLabels Q label tau,((labelFiber Q label i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ smallLabels Q label tau,tau := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ = ((smallLabels Q label tau).card : ℝ)*tau := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ (smallLabels Q label tau)) htau

end ErdosInverseCells

end

section

namespace ErdosGeometricValueCells

theorem coordinate_bounds {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    0 < q ∧ 0 ≤ coordinate B xi q ∧ coordinate B xi q ≤ k := by
  have hF : 0 < 1+xi := by linarith
  have hpow : 0 < (1+xi)^k := pow_pos hF _
  have hq : 0 < q := (div_pos hB hpow).trans_le hlo
  have hL : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hrat : 1 ≤ B/q := (one_le_div hq).mpr hhi
  have hratUpper : B/q ≤ (1+xi)^k := by
    apply (div_le_iff₀ hq).mpr
    have h := (div_le_iff₀ hpow).mp hlo
    simpa only [mul_comm] using h
  refine ⟨hq, div_nonneg (Real.log_nonneg hrat) hL.le, ?_⟩
  have hlog := Real.log_le_log (div_pos hB hq) hratUpper
  rw [Real.log_pow] at hlog
  exact (div_le_iff₀ hL).mpr hlog

theorem valueIndex_eq_floor {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    (valueIndex B xi k q).val = ⌊coordinate B xi q⌋₊ := by
  have hs := coordinate_bounds hB hxi hlo hhi
  have hfloor : ⌊coordinate B xi q⌋₊ ≤ k := by
    exact_mod_cast (Nat.floor_le hs.2.1).trans hs.2.2
  exact min_eq_right hfloor

theorem valueIndex_interval {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    B/(1+xi)^((valueIndex B xi k q).val+1) < q ∧
      q ≤ B/(1+xi)^(valueIndex B xi k q).val := by
  have hs := coordinate_bounds hB hxi hlo hhi
  have hF : 0 < 1+xi := by linarith
  have hL : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hfloor := valueIndex_eq_floor hB hxi hlo hhi
  have hl : ((valueIndex B xi k q).val : ℝ) ≤ coordinate B xi q := by
    rw [hfloor]
    exact Nat.floor_le hs.2.1
  have hu : coordinate B xi q < ((valueIndex B xi k q).val : ℝ)+1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one _
  have hlogLower := (le_div_iff₀ hL).mp hl
  have hlogUpper := (div_lt_iff₀ hL).mp hu
  have hpLower := Real.exp_le_exp.mpr hlogLower
  rw [Real.exp_nat_mul, Real.exp_log hF, Real.exp_log (div_pos hB hs.1)] at hpLower
  have hpUpper := Real.exp_lt_exp.mpr hlogUpper
  have he : (((valueIndex B xi k q).val : ℝ)+1)*Real.log (1+xi) =
      (((valueIndex B xi k q).val+1 : ℕ) : ℝ)*Real.log (1+xi) := by norm_num
  rw [he, Real.exp_nat_mul, Real.exp_log hF, Real.exp_log (div_pos hB hs.1)] at hpUpper
  constructor
  · apply (div_lt_iff₀ (pow_pos hF _)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hs.1).mp hpUpper
  · apply (le_div_iff₀ (pow_pos hF _)).mpr
    simpa only [mul_comm] using (le_div_iff₀ hs.1).mp hpLower

end ErdosGeometricValueCells

end

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem exists_dense_retained_fiber {ι : Type*} [Fintype ι]
    (Q : Finset ℕ) (label : ℕ → ι) (tau sigma : ℝ) (hsigma : 0 ≤ sigma)
    (w f : ℕ → ℝ) (hw : ∀ q ∈ Q,0 ≤ w q) (hf : ∀ q ∈ Q,f q ≤ w q)
    (hmass : sigma*(∑ q ∈ Q,w q) < ∑ q ∈ Q,f q)
    (hdiscard : (∑ q ∈ discardedPoints Q label tau,w q) ≤ (sigma/2)*(∑ q ∈ Q,w q)) :
    ∃ i : ι,tau ≤ ((labelFiber Q label i).card : ℝ) ∧
      (sigma/2)*(∑ q ∈ labelFiber Q label i,w q) < ∑ q ∈ labelFiber Q label i,f q := by
  classical
  by_contra hno
  push Not at hno
  have hcell : ∀ i : ι,(∑ q ∈ labelFiber Q label i,f q) ≤
      (sigma/2)*(∑ q ∈ labelFiber Q label i,w q)+
        (if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0) := by
    intro i
    have hWi : 0 ≤ ∑ q ∈ labelFiber Q label i,w q :=
      Finset.sum_nonneg (fun q hq => hw q (labelFiber_subset Q label i hq))
    by_cases hi : ((labelFiber Q label i).card : ℝ) < tau
    · rw [ite_eq_left hi]
      have hfi := Finset.sum_le_sum (fun q hq => hf q (labelFiber_subset Q label i hq))
      have hprod := mul_nonneg (show 0 ≤ sigma/2 by positivity) hWi
      linarith
    · rw [ite_eq_right hi,add_zero]
      exact hno i (le_of_not_gt hi)
  have hsmall : (∑ i : ι,if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0) =
      ∑ q ∈ discardedPoints Q label tau,w q := by
    calc
      _ = ∑ i ∈ smallLabels Q label tau,∑ q ∈ labelFiber Q label i,w q := by
        simp only [smallLabels,Finset.sum_filter]
      _ = _ := sum_small_fibers Q label tau w
  have hall : (∑ q ∈ Q,f q) ≤ (sigma/2)*(∑ q ∈ Q,w q)+∑ q ∈ discardedPoints Q label tau,w q := by
    calc
      _ = ∑ i : ι,∑ q ∈ labelFiber Q label i,f q := (sum_label_fibers Q label f).symm
      _ ≤ ∑ i : ι,((sigma/2)*(∑ q ∈ labelFiber Q label i,w q)+
          (if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0)) :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_label_fibers,hsmall]
  linarith

end ErdosInverseCells

end

section

namespace ErdosInverseCells
open ErdosInverseHits ErdosGeometricValueCells
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem initialLabel_card (k M0 : ℕ) [NeZero M0] :
    Fintype.card (InitialLabel k M0) = (k+1)*M0^2 := by
  simp only [InitialLabel,Fintype.card_prod,Fintype.card_fin,ZMod.card]
  ring

theorem same_initial_label (a : ℕ → ℕ) (B xi : ℝ) (k M0 q r : ℕ)
    (he : initialLabel a B xi k M0 q = initialLabel a B xi k M0 r) :
    valueIndex B xi k (q : ℝ) = valueIndex B xi k (r : ℝ) ∧
      Int.ModEq (M0 : ℤ) (q : ℤ) (r : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit r a : ℤ) := by
  have hi := congrArg (fun i : InitialLabel k M0 => i.1) he
  have hq := congrArg (fun i : InitialLabel k M0 => i.2.1) he
  have hb := congrArg (fun i : InitialLabel k M0 => i.2.2) he
  exact ⟨hi,Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff q r M0).mp hq),
    Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff (cofactorHit q a) (cofactorHit r a) M0).mp hb)⟩

theorem initial_cell_interval (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (hB : 0 < B) (hxi : 0 < xi)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (i : InitialLabel k M0) (q : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i) :
    q ∈ Q ∧ 0 < (q : ℝ) ∧ (q : ℝ) ≤ cellUpper B xi i ∧ cellUpper B xi i ≤ (1+xi)*(q : ℝ) := by
  have hm := (mem_labelFiber Q (initialLabel a B xi k M0) i q).mp hq
  have hi : valueIndex B xi k (q : ℝ) = i.1 := congrArg (fun j : InitialLabel k M0 => j.1) hm.2
  have hinterval := valueIndex_interval hB hxi (hQ q hm.1).1 (hQ q hm.1).2
  rw [hi] at hinterval
  have hqpos : 0 < (q : ℝ) := (coordinate_bounds hB hxi (hQ q hm.1).1 (hQ q hm.1).2).1
  have hlow : cellUpper B xi i/(1+xi) < (q : ℝ) := by
    unfold cellUpper
    rw [div_div,← pow_succ]
    exact hinterval.1
  refine ⟨hm.1,hqpos,hinterval.2,?_⟩
  have hh := (div_lt_iff₀ (by linarith : 0 < 1+xi)).mp hlow
  nlinarith

end ErdosInverseCells

end

section

namespace ErdosInverseCells

theorem mem_initialCell (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) (q : ℕ) :
    q ∈ initialCell Q a B xi k M0 i ↔ q ∈ Q ∧ initialLabel a B xi k M0 q = i :=
  mem_labelFiber Q (initialLabel a B xi k M0) i q

theorem initial_cell_congruences (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) (q r : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i)
    (hr : r ∈ initialCell Q a B xi k M0 i) :
    Int.ModEq (M0 : ℤ) (q : ℤ) (r : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit r a : ℤ) := by
  have hq' := (mem_initialCell Q a B xi k M0 i q).mp hq
  have hr' := (mem_initialCell Q a B xi k M0 i r).mp hr
  exact (same_initial_label a B xi k M0 q r (hq'.2.trans hr'.2.symm)).2

theorem initial_cell_weight_spread (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (hB : 0 < B) (hxi : 0 < xi)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (i : InitialLabel k M0) (q r : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i)
    (hr : r ∈ initialCell Q a B xi k M0 i) :
    (q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹ := by
  have hq' := initial_cell_interval Q a B xi k M0 hB hxi hQ i q hq
  have hr' := initial_cell_interval Q a B xi k M0 hB hxi hQ i r hr
  have hratio : (r : ℝ) ≤ (1+xi)*(q : ℝ) := hr'.2.2.1.trans hq'.2.2.2
  have hh : (1 : ℝ)/(q : ℝ) ≤ (1+xi)/(r : ℝ) :=
    (div_le_div_iff₀ hq'.2.1 hr'.2.1).mpr (by simpa only [one_mul] using hratio)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hh

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler

theorem source_initial_label_count (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ k : ℕ,(k : ℝ) ≤ C*Real.log (sourceB z) →
      (((k+1)*(smallModulus (sourceW z))^2 : ℕ) : ℝ) ≤ (sourceZ z)^eps := by
  have hZ := (tendsto_rpow_atTop (by positivity : 0 < eps/2)).comp sourceZ_tendsto_atTop
  filter_upwards [source_log_budget,smallModulus_mul_log_power 2 1 (eps/2) (by positivity),
    hZ.eventually_ge_atTop (C+1),Real.tendsto_log_atTop.eventually_ge_atTop 1] with z hs hm hcoef hL1
  intro k hk
  have hkL : (k : ℝ) ≤ C*Real.log z := by
    have hh := hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
    have hlog := Real.log_le_sub_one_of_pos hs.1
    have hL : Real.log (Real.log z) ≤ Real.log z := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left hL hC)
  have hk1 : (k : ℝ)+1 ≤ (C+1)*Real.log z := by nlinarith
  have hM : (smallModulus (sourceW z) : ℝ)^2*Real.log z ≤ (sourceZ z)^(eps/2) := by
    simpa only [pow_one] using hm
  have hZpos : 0 < sourceZ z := Real.exp_pos _
  calc
    _ = ((k : ℝ)+1)*(smallModulus (sourceW z) : ℝ)^2 := by push_cast;rfl
    _ ≤ ((C+1)*Real.log z)*(smallModulus (sourceW z) : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hk1 (sq_nonneg _)
    _ = (C+1)*((smallModulus (sourceW z) : ℝ)^2*Real.log z) := by ring
    _ ≤ (sourceZ z)^(eps/2)*(sourceZ z)^(eps/2) :=
      mul_le_mul hcoef hM (by positivity) (Real.rpow_nonneg hZpos.le _)
    _ = (sourceZ z)^eps := by
      rw [← Real.rpow_add hZpos]
      congr 1
      ring

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceInitialDiscard
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells

theorem discard_coefficient_bound (S Z eps : ℝ) (n labels : ℕ) (hS : 0 < S) (hZ : 0 < Z)
    (hn : S/Z^eps ≤ (n : ℝ)) (hl : (labels : ℝ) ≤ Z^eps) :
    (labels : ℝ)*(S/Z)*Z^eps/(n : ℝ) ≤ Z^(3*eps-1) := by
  have hZpow : 0 < Z^eps := Real.rpow_pos_of_pos hZ eps
  have hn0 : (0 : ℝ) < n := (div_pos hS hZpow).trans_le hn
  calc
    _ ≤ Z^eps*(S/Z)*Z^eps/(n : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hl (div_pos hS hZ).le) hZpow.le) hn0.le
    _ ≤ Z^eps*(S/Z)*Z^eps/(S/Z^eps) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hS hZpow) hn
    _ = (S*S⁻¹)*(Z^eps*Z^eps*Z^eps/Z) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = Z^eps*Z^eps*Z^eps/Z := by rw [mul_inv_cancel₀ hS.ne',one_mul]
    _ = Z^(eps+eps+eps-1) := by
      rw [← Real.rpow_add hZ,← Real.rpow_add hZ]
      simpa only [Real.rpow_one] using (Real.rpow_sub hZ (eps+eps+eps) 1).symm
    _ = Z^(3*eps-1) := by congr 1;ring

end ErdosInverseCells

end

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem subset_weight_spread {α : Type*} (Q D : Finset α) (hD : D ⊆ Q) (hQ : 0 < Q.card)
    (w : α → ℝ) (G : ℝ) (hspread : ∀ q ∈ Q,∀ r ∈ Q,w q ≤ G*w r) :
    (∑ q ∈ D,w q) ≤ ((D.card : ℝ)*G/(Q.card : ℝ))*(∑ r ∈ Q,w r) := by
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast hQ
  have hdouble : (Q.card : ℝ)*(∑ q ∈ D,w q) ≤ (D.card : ℝ)*G*(∑ r ∈ Q,w r) := by
    calc
      _ = ∑ q ∈ D,∑ _r ∈ Q,w q := by
        simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      _ ≤ ∑ q ∈ D,∑ r ∈ Q,G*w r :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hspread q (hD hq) r hr))
      _ = _ := by
        simp only [← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
        ring
  calc
    _ ≤ ((D.card : ℝ)*G*(∑ r ∈ Q,w r))/(Q.card : ℝ) :=
      (le_div_iff₀ hQpos).mpr (by nlinarith [hdouble])
    _ = _ := by ring

theorem discarded_weight_bound {ι : Type*} [Fintype ι]
    (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (htau : 0 ≤ tau) (hQ : 0 < Q.card)
    (w : ℕ → ℝ) (hw : ∀ q ∈ Q,0 ≤ w q) (G : ℝ) (hG : 0 ≤ G)
    (hspread : ∀ q ∈ Q,∀ r ∈ Q,w q ≤ G*w r) :
    (∑ q ∈ discardedPoints Q label tau,w q) ≤
      ((Fintype.card ι : ℝ)*tau*G/(Q.card : ℝ))*(∑ q ∈ Q,w q) := by
  have hsum : 0 ≤ ∑ q ∈ Q,w q := Finset.sum_nonneg hw
  have hcard := discardedPoints_card_bound Q label tau htau
  calc
    _ ≤ (((discardedPoints Q label tau).card : ℝ)*G/(Q.card : ℝ))*(∑ q ∈ Q,w q) :=
      subset_weight_spread Q _ (discardedPoints_subset Q label tau) hQ w G hspread
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hG) (Nat.cast_nonneg _)) hsum

end ErdosInverseCells

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

theorem source_initial_discard_power (C xi eps : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      let Q := cofactorChoices (actualBins z xi) m
      let S := cofactorScale z xi m
      let k := ∑ i,m i
      (∑ q ∈ initialDiscarded Q a S xi k (sourceW z) (sourceZ z),(q : ℝ)⁻¹) ≤
        (sourceZ z)^(3*eps-1)*(∑ q ∈ Q,(q : ℝ)⁻¹) := by
  filter_upwards [source_cofactor_cell_data C xi eps hC hxi hxi1 heps,
    source_initial_label_count C eps hC heps,source_cofactor_weight_variation C xi eps hC hxi hxi1 heps]
    with z hc hl hw
  intro m a hm
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ i,m i
  let : NeZero (smallModulus (sourceW z)) := ⟨(smallModulus_pos _).ne'⟩
  have hdata := hc m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hlabel : (Fintype.card (InitialLabel k (smallModulus (sourceW z))) : ℝ) ≤ (sourceZ z)^eps := by
    rw [initialLabel_card]
    exact hl k hm
  have hspread : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (sourceZ z)^eps*(r : ℝ)⁻¹ :=
    fun q hq r hr => (hw m hm q r hq hr).2
  have hmass : 0 ≤ ∑ q ∈ Q,(q : ℝ)⁻¹ := by positivity
  have hdiscard := discarded_weight_bound Q (initialLabel a S xi k (smallModulus (sourceW z)))
    (S/sourceZ z) (div_pos hdata.1 hZ).le hdata.2.1 (fun q => (q : ℝ)⁻¹)
    (fun _ _ => by positivity) ((sourceZ z)^eps) (Real.rpow_nonneg hZ.le _) hspread
  have hcoef := discard_coefficient_bound S (sourceZ z) eps Q.card
    (Fintype.card (InitialLabel k (smallModulus (sourceW z)))) hdata.1 hZ hdata.2.2.1 hlabel
  exact hdiscard.trans (mul_le_mul_of_nonneg_right hcoef hmass)

theorem source_initial_discard_small (C xi tolerance : ℝ) (hC : 0 ≤ C) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (ht : 0 < tolerance) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
      ((∑ i,m i : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
      let Q := cofactorChoices (actualBins z xi) m
      let S := cofactorScale z xi m
      let k := ∑ i,m i
      (∑ q ∈ initialDiscarded Q a S xi k (sourceW z) (sourceZ z),(q : ℝ)⁻¹) ≤
        tolerance*(∑ q ∈ Q,(q : ℝ)⁻¹) := by
  have hT := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5/8)).comp sourceZ_tendsto_atTop
  have hs := (tendsto_order.mp hT).2 tolerance ht
  filter_upwards [source_initial_discard_power C xi (1/8) hC hxi hxi1 (by norm_num),hs] with z hc hz
  intro m a hm
  have hh := hc m a hm
  norm_num only at hh
  have hz' : (sourceZ z)^(-((5 : ℝ)/8)) < tolerance := hz
  have hp : (sourceZ z)^(-((5 : ℝ)/8)) ≤ tolerance := by linarith
  exact hh.trans (mul_le_mul_of_nonneg_right hp (by positivity))

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_TripleWeightDensity
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem weighted_to_count_density {α : Type*} (A B : Finset α) (hB : B ⊆ A) (hA : 0 < A.card)
    (w : α → ℝ) (G rho : ℝ) (hG : 0 < G) (hTotal : 0 < ∑ a ∈ A,w a)
    (hspread : ∀ a ∈ A,∀ b ∈ A,w a ≤ G*w b)
    (hweighted : rho*(∑ a ∈ A,w a) ≤ ∑ b ∈ B,w b) :
    (rho/G)*(A.card : ℝ) ≤ (B.card : ℝ) := by
  have hspreadSum := subset_weight_spread A B hB hA w G hspread
  have hcoef : rho ≤ (B.card : ℝ)*G/(A.card : ℝ) :=
    le_of_mul_le_mul_right (hweighted.trans hspreadSum) hTotal
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hmul := (le_div_iff₀ hApos).mp hcoef
  calc
    _ = (rho*(A.card : ℝ))/G := by ring
    _ ≤ (B.card : ℝ) := (div_le_iff₀ hG).mpr hmul

end ErdosInverseCells

end

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem triple_weight_spread (P Q U : Finset ℕ) (xi : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hP : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hQ : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hU : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹) :
    ∀ x ∈ tripleSpace P Q U,∀ y ∈ tripleSpace P Q U,tripleWeight x ≤ 8*tripleWeight y := by
  intro x hx y hy
  have hx' : x.1.1 ∈ P ∧ x.1.2 ∈ Q ∧ x.2 ∈ U := by
    simpa only [tripleSpace,Finset.mem_product,and_assoc] using hx
  have hy' : y.1.1 ∈ P ∧ y.1.2 ∈ Q ∧ y.2 ∈ U := by
    simpa only [tripleSpace,Finset.mem_product,and_assoc] using hy
  have h1 := hP _ hx'.1 _ hy'.1
  have h2 := hQ _ hx'.2.1 _ hy'.2.1
  have h3 := hU _ hx'.2.2 _ hy'.2.2
  have hc : (1+xi)^3 ≤ (8 : ℝ) := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 1+xi) (by linarith : 1+xi ≤ 2) 3
    norm_num at hh
    exact hh
  calc
    _ ≤ ((1+xi)*(y.1.1 : ℝ)⁻¹)*((1+xi)*(y.1.2 : ℝ)⁻¹)*((1+xi)*(y.2 : ℝ)⁻¹) :=
      mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = (1+xi)^3*tripleWeight y := by unfold tripleWeight;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (tripleWeight_nonneg y)

theorem triple_weighted_to_count (P Q U : Finset ℕ) (xi sigma : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (witness : (ℕ × ℕ) → ℕ → Prop)
    (hPpos : 0 < harmonicMass P) (hQpos : 0 < harmonicMass Q) (hUpos : 0 < harmonicMass U)
    (hP : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hQ : ∀ q ∈ Q,∀ r ∈ Q,(q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hU : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hweighted : (sigma/2)*(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ weightedWitness P Q U witness) :
    (sigma/16)*((P.product Q).card : ℝ)*(U.card : ℝ) ≤
      ((witnessPairs (P.product Q) U witness).card : ℝ) := by
  have hTotal : 0 < ∑ x ∈ tripleSpace P Q U,tripleWeight x := by
    rw [triple_weight_sum]
    exact mul_pos (mul_pos hPpos hQpos) hUpos
  have hA : 0 < (tripleSpace P Q U).card := by
    by_contra hn
    have he : tripleSpace P Q U = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he,Finset.sum_empty] at hTotal
    linarith
  have hsub : witnessPairs (P.product Q) U witness ⊆ tripleSpace P Q U := Finset.filter_subset _ _
  have hh := weighted_to_count_density (tripleSpace P Q U) (witnessPairs (P.product Q) U witness)
    hsub hA tripleWeight 8 (sigma/2) (by norm_num) hTotal (triple_weight_spread P Q U xi hxi hxi1 hP hQ hU)
    (by simpa only [triple_weight_sum,weightedWitness] using hweighted)
  simpa only [tripleSpace,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,div_div,show (2 : ℝ)*8 = 16 by norm_num,mul_assoc] using hh

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceExtensionScale
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
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem sourceW_log_bounds : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < Real.log z ∧ (Real.log z)^((1 : ℝ)/2) ≤ sourceW z ∧ sourceW z ≤ Real.log z := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with z hh hLL hz
  have hL : 0 < Real.log z := Real.log_pos hz
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLLpos : 0 < Real.log (Real.log z) := by linarith
  have hbound : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
      abs_of_nonneg (Real.rpow_nonneg hL.le ((1 : ℝ)/2)),one_mul] using hh
  have heq : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
    rw [← Real.rpow_add hL]
    norm_num
  refine ⟨hz,hL,?_,?_⟩
  · apply (le_div_iff₀ (sq_pos_of_pos hLLpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hL.le ((1 : ℝ)/2))]
  · exact div_le_self hL.le (by nlinarith)

theorem sourceW_le_power (alpha : ℝ) (ha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,sourceW z ≤ z^alpha := by
  have hs := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).bound zero_lt_one
  filter_upwards [sourceW_log_bounds,hs] with z hz hh
  have hlog : Real.log z ≤ z^alpha := by
    simpa only [Real.norm_eq_abs,Real.rpow_one,abs_of_pos hz.2.1,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hz.1] : 0 ≤ z) alpha),one_mul] using hh
  exact hz.2.2.2.trans hlog

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoxHeightBudget
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
namespace ErdosInverseBoxHeight

theorem small_power_height {z Sq R Z : ℝ} (hz : 4 ≤ z)
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hSqz : Sq ≤ z^((21:ℝ)/10)) (hRz : R ≤ z^((1:ℝ)/100))
    (hZz : Z ≤ z^((1:ℝ)/100)) : 2*Sq*R^2*Z^20 ≤ z^3 := by
  have hz0 : 0 ≤ z := by linarith
  have hzpos : 0 < z := by linarith
  have htwo : (2:ℝ) ≤ z^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) hz0).mpr (by norm_num; exact hz)
  have hRp : R^2 ≤ z^((2:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^2 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  have hZp : Z^20 ≤ z^((20:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^20 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  calc
    _ ≤ z^((1:ℝ)/2)*z^((21:ℝ)/10)*z^((2:ℝ)/100)*z^((20:ℝ)/100) := by gcongr
    _ = z^((141:ℝ)/50) := by
      rw [← Real.rpow_add hzpos,← Real.rpow_add hzpos,← Real.rpow_add hzpos]
      norm_num
    _ ≤ z^3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ z)
        (by norm_num : (141:ℝ)/50 ≤ 3)
      norm_num at h ⊢
      exact h

theorem uniform_box_height (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ Sq R B xi q : ℝ,
      0 ≤ Sq → 0 ≤ R → 1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      0 < q → q ≤ z^2 → Sq/q ≤ (1+xi)^(C*Real.log B) → R ≤ z^((1:ℝ)/100) →
      2*Sq*R^2*(sourceZ z)^20 ≤ z^3 := by
  filter_upwards [uniform_bin_inflation C hC,sourceZ_le_small_power,eventually_ge_atTop (4:ℝ)]
    with z hInfl hZ hz
  refine ⟨hInfl.1,?_⟩
  intro Sq R B xi q hSq hR hB hBL hxi0 hxi1 hq hqz hinfl hRz
  have hBpow := hInfl.2 B xi hB hBL hxi0 hxi1
  have hSqz : Sq ≤ z^((21:ℝ)/10) := by
    have hSqbound := (div_le_iff₀ hq).mp (hinfl.trans hBpow)
    calc
      _ ≤ z^((1:ℝ)/10)*q := hSqbound
      _ ≤ z^((1:ℝ)/10)*z^2 :=
        mul_le_mul_of_nonneg_left hqz (Real.rpow_nonneg (by linarith) _)
      _ = _ := by
        rw [← Real.rpow_natCast z 2,← Real.rpow_add (by linarith : 0 < z)]
        norm_num
  exact small_power_height hz hSq hR hZ.2.1.le hSqz hRz hZ.2.2

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualPointSlopes
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
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem sampleGamma_pos (beta : ℝ) (h : ℕ) (hb : 0 < beta) : 0 < sampleGamma beta h := by
  unfold sampleGamma
  positivity

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceDenseCellContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosCofactorChoices
attribute [local instance] Classical.decEq

theorem cofactor_coprime_excluded_bin {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i : ι) (hi : m i = 0) (q : ℕ) (hq : q ∈ cofactorChoices P m) :
    ∀ p ∈ P i,q.Coprime p := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hs := (mem_selections P m f).mp hf
  have hz : f i = ∅ := Finset.card_eq_zero.mp ((hs i).2.trans hi)
  have hrec := prime_factor_bin_recovery P m hP hd f hf i
  rw [hz] at hrec
  intro p hp
  apply Nat.Coprime.symm
  apply (hP i p hp).coprime_iff_not_dvd.mpr
  intro hdiv
  have hm : p ∈ (selectionProduct f).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hP i p hp,hdiv,(selectionProduct_pos P hP f (fun j => (hs j).1)).ne'⟩
  have he := Finset.mem_inter.mpr ⟨hm,hp⟩
  rw [hrec] at he
  exact Finset.notMem_empty p he

theorem cofactor_coprime_small {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (w : ℝ) (hlarge : ∀ i,∀ p ∈ P i,w < (p : ℝ))
    (q : ℕ) (hq : q ∈ cofactorChoices P m) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    q.Coprime t := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hs := (mem_selections P m f).mp hf
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply (Nat.coprime_primes (hP i p ((hs i).1 hp)) ht).mpr
  intro he
  have hh := hlarge i p ((hs i).1 hp)
  subst p
  linarith

theorem distinct_bins_coprime {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i,∀ p ∈ P i,p.Prime)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (i j : ι) (hij : i ≠ j) :
    ∀ p ∈ P i,∀ u ∈ P j,p.Coprime u := by
  intro p hp u hu
  apply (Nat.coprime_primes (hP i p hp) (hP j u hu)).mpr
  intro he
  exact Finset.disjoint_left.mp (hd hij) hp (he.symm ▸ hu)

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement

theorem parent_product_le_of_child_log (Y p q u : ℕ) (w a : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hu : 1 ≤ u) (hw : 1 < w) (ha : 0 < a)
    (hlog : 3*a/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    (p : ℝ)*(q : ℝ) ≤ (Y : ℝ) := by
  have hwlog : 0 < Real.log w := Real.log_pos hw
  have hpositive : 0 < Real.log ((Y : ℝ)/((p : ℝ)*q*u)) := by
    have hh := (le_div_iff₀ hwlog).mp hlog
    have hleft : 0 < (3*a/4)*Real.log w := by positivity
    exact hleft.trans_le hh
  have hden : 0 < (p : ℝ)*q*u := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hp hq) (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hrat0 : 0 ≤ (Y : ℝ)/((p : ℝ)*q*u) := div_nonneg (Nat.cast_nonneg _) hden.le
  have hrat1 : 1 < (Y : ℝ)/((p : ℝ)*q*u) := (Real.log_pos_iff hrat0).mp hpositive
  have hh := (lt_div_iff₀ hden).mp hrat1
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hmul := mul_le_mul_of_nonneg_left huR (show 0 ≤ (p : ℝ)*q by positivity)
  nlinarith

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ActualCofactorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseBoxApplication
open ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement ErdosInverseBoxHeight
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition

theorem actual_excluded_bin_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (i : Fin (binCount (sourceW z) z xi)) (hi : m i = 0)
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    ∀ p ∈ actualBins z xi i,q.Coprime p :=
  cofactor_coprime_excluded_bin (actualBins z xi) m
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) i hi q hq

theorem actual_distinct_bins_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (i j : Fin (binCount (sourceW z) z xi)) (hij : i ≠ j) :
    ∀ p ∈ actualBins z xi i,∀ u ∈ actualBins z xi j,p.Coprime u :=
  distinct_bins_coprime (actualBins z xi)
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) i j hij

theorem actual_parent_small_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m)
    (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
    ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q).Coprime t := by
  intro t ht htw
  have hqcop := cofactor_coprime_small (actualBins z xi) m
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1) (sourceW z)
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).2.1) q hq t ht htw
  apply Nat.Coprime.mul_left _ hqcop
  have hps := bin_prime_in_source hw hwz hxi i hp
  apply (Nat.coprime_primes hps.1 ht).mpr
  intro he
  subst p
  linarith [hps.2.1]

theorem actual_source_cofactor_inflation {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (Clen : ℝ) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (hm : ((∑ i,m i : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z))
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    1 ≤ cofactorScale z xi m/(q : ℝ) ∧
      cofactorScale z xi m/(q : ℝ) ≤
        (1+effectiveWidth (sourceW z) z xi)^(Clen*Real.log (sourceB z)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast actual_cofactor_positive hw hwz hxi m q hq
  have htheta := effectiveWidth_pos hw hwz hxi
  have hF : 0 < 1+effectiveWidth (sourceW z) z xi := by linarith
  have hrange := actual_cofactor_effective_range hw hwz hxi m q hq
  refine ⟨(one_le_div hqpos).mpr hrange.2,?_⟩
  calc
    _ ≤ (1+effectiveWidth (sourceW z) z xi)^(∑ i,m i) := by
      apply (div_le_iff₀ hqpos).mpr
      have hh := (div_le_iff₀ (pow_pos hF _)).mp hrange.1
      nlinarith
    _ = (1+effectiveWidth (sourceW z) z xi)^((∑ i,m i : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hm

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualBoxHarmonicInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem retained_initial_cell (P Q U : Finset ℕ) (a : ℕ → ℕ) (B xi Z sigma : ℝ) (k M0 : ℕ) [NeZero M0]
    (hB : 0 < B) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hZ : 0 < Z) (hsigma : 0 ≤ sigma)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (witness : (ℕ × ℕ) → ℕ → Prop) (hPpos : 0 < harmonicMass P) (hUpos : 0 < harmonicMass U)
    (hPspread : ∀ p ∈ P,∀ r ∈ P,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hUspread : ∀ u ∈ U,∀ r ∈ U,(u : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹)
    (hBad : sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) < weightedWitness P Q U witness)
    (hDiscard : (∑ q ∈ discardedPoints Q (initialLabel a B xi k M0) (B/Z),(q : ℝ)⁻¹) ≤
      (sigma/2)*(∑ q ∈ Q,(q : ℝ)⁻¹)) :
    ∃ i : InitialLabel k M0,B/Z ≤ ((initialCell Q a B xi k M0 i).card : ℝ) ∧
      (initialCell Q a B xi k M0 i).Nonempty ∧
      (sigma/16)*((P.product (initialCell Q a B xi k M0 i)).card : ℝ)*(U.card : ℝ) ≤
        ((witnessPairs (P.product (initialCell Q a B xi k M0 i)) U witness).card : ℝ) := by
  have hDen := mul_pos hPpos hUpos
  have hCond := condition_harmonic_density P Q U witness sigma hDen hBad
  obtain ⟨i,hlarge,hdense⟩ := exists_dense_retained_fiber Q (initialLabel a B xi k M0) (B/Z) sigma hsigma
    (fun q => (q : ℝ)⁻¹) (fun q => (q : ℝ)⁻¹*conditionalReward P U witness q)
    (fun _ _ => by positivity) (fun q _ => conditioned_reward_upper P U witness hDen q) hCond hDiscard
  have hcardR : (0 : ℝ) < (initialCell Q a B xi k M0 i).card := (div_pos hB hZ).trans_le hlarge
  have hcard : 0 < (initialCell Q a B xi k M0 i).card := by exact_mod_cast hcardR
  have hne := Finset.card_pos.mp hcard
  have hCpos : 0 < harmonicMass (initialCell Q a B xi k M0 i) := by
    apply harmonicMass_pos _ hne
    intro q hq
    exact_mod_cast (initial_cell_interval Q a B xi k M0 hB hxi hQ i q hq).2.1
  have hWeighted := uncondition_harmonic_density P (initialCell Q a B xi k M0 i) U witness (sigma/2) hDen hdense
  exact ⟨i,hlarge,hne,triple_weighted_to_count P (initialCell Q a B xi k M0 i) U xi sigma hxi.le hxi1
    witness hPpos hCpos hUpos hPspread
    (fun q hq r hr => initial_cell_weight_spread Q a B xi k M0 hB hxi hQ i q r hq hr) hUspread hWeighted.le⟩

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open NumberTheoryLean ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale

theorem source_dense_initial_cell (C xi sigma alpha delta cp : ℝ) (hC : 0 ≤ C)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hsigma : 0 < sigma) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU : ℝ,
      z^alpha ≤ R → sourceW z ≤ U → xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ) (a : ℕ → ℕ),
        ((∑ j,m j : ℕ) : ℝ) ≤ C*Real.log (sourceB z) →
        let Q := cofactorChoices (actualBins z xi) m
        let S := cofactorScale z xi m
        let k := ∑ j,m j
        let P := primeBin R thetaP
        let Uset := primeBin U thetaU
        let M0 := smallModulus (sourceW z)
        let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
        sigma*(harmonicMass P*harmonicMass Q*harmonicMass Uset) < weightedWitness P Q Uset witness →
        ∃ (i : InitialLabel k M0) (q0 : ℕ),
          q0 ∈ initialCell Q a S xi k M0 i ∧
          S/sourceZ z ≤ ((initialCell Q a S xi k M0 i).card : ℝ) ∧
          (sigma/16)*((P.product (initialCell Q a S xi k M0 i)).card : ℝ)*(Uset.card : ℝ) ≤
            ((witnessPairs (P.product (initialCell Q a S xi k M0 i)) Uset witness).card : ℝ) ∧
          (initialCell Q a S xi k M0 i ⊆ Q) ∧
          ∀ q ∈ initialCell Q a S xi k M0 i,
            0 < q ∧ Squarefree q ∧ (q : ℝ) ≤ cellUpper S xi i ∧ cellUpper S xi i ≤ (1+xi)*(q : ℝ) ∧
              Int.ModEq (M0 : ℤ) (q : ℤ) (q0 : ℤ) ∧
              Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit q0 a : ℤ) := by
  filter_upwards [source_initial_discard_small C xi (sigma/2) hC hxi hxi1 (by positivity),
    source_cofactor_cell_data C xi 1 hC hxi hxi1 zero_lt_one,source_span_geometry,
    source_sample_population xi 1 0 hxi hxi1,sourceW_le_power alpha halpha,eventually_gt_atTop (1 : ℝ)]
    with z hdiscard hdata hspan hpop hWR hz
  refine ⟨hz,?_⟩
  intro R thetaP U thetaU hR hWU hPlow hPhigh hUlow hUhigh m a hm
  dsimp only
  intro hBad
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ j,m j
  let P := primeBin R thetaP
  let Uset := primeBin U thetaU
  let M0 := smallModulus (sourceW z)
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
  let : NeZero M0 := ⟨(smallModulus_pos _).ne'⟩
  have hd := hdata m hm
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hzpos : 0 < z := by linarith
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have hUpos : 0 < U := hspan.1.trans_le hWU
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPn : P.Nonempty := Finset.card_pos.mp (hpop R thetaP (hWR.trans hR) hPlow hPhigh).1
  have hUn : Uset.Nonempty := Finset.card_pos.mp (hpop U thetaU hWU hUlow hUhigh).1
  have hPmass : 0 < harmonicMass P := harmonicMass_pos P hPn
    (fun p hp => ((mem_primeBin hRpos.le hthetaP p).mp hp).1.pos)
  have hUmass : 0 < harmonicMass Uset := harmonicMass_pos Uset hUn
    (fun u hu => ((mem_primeBin hUpos.le hthetaU u).mp hu).1.pos)
  have hQrange : ∀ q ∈ Q,S/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ S :=
    fun q hq => actual_cofactor_range hspan.1 hspan.2.1 hxi m q hq
  have hDisc : (∑ q ∈ discardedPoints Q (initialLabel a S xi k M0) (S/sourceZ z),(q : ℝ)⁻¹) ≤
      (sigma/2)*(∑ q ∈ Q,(q : ℝ)⁻¹) := hdiscard m a hm
  obtain ⟨i,hlarge,hne,hDense⟩ := retained_initial_cell P Q Uset a S xi (sourceZ z) sigma k M0
    hd.1 hxi hxi1 hZ hsigma.le hQrange witness hPmass hUmass
    (prime_bin_weight_spread R thetaP xi hRpos hthetaP hxi.le hPhigh)
    (prime_bin_weight_spread U thetaU xi hUpos hthetaU hxi.le hUhigh) hBad hDisc
  obtain ⟨q0,hq0⟩ := hne
  refine ⟨i,q0,hq0,hlarge,hDense,labelFiber_subset Q (initialLabel a S xi k M0) i,?_⟩
  intro q hq
  have hqQ := (mem_initialCell Q a S xi k M0 i q).mp hq |>.1
  have hqs := hd.2.2.2 q hqQ
  have hinterval := initial_cell_interval Q a S xi k M0 hd.1 hxi hQrange i q hq
  have hcong := initial_cell_congruences Q a S xi k M0 i q q0 hq hq0
  exact ⟨hqs.1,hqs.2,hinterval.2.2.1,hinterval.2.2.2,hcong.1,hcong.2⟩

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem actual_box_nonstructured_harmonic (Clen Cparent aStar K alpha delta sigma : ℝ) (h : ℕ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,
        ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
          (i j : Fin (binCount (sourceW z) z xi)),
          i ≠ j → m i = 0 → m j = 0 →
          ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
          ∀ a : ℕ → ℕ,
          let R := lower (sourceW z) z xi i
          let U := lower (sourceW z) z xi j
          let P := actualBins z xi i
          let Uset := actualBins z xi j
          let Q := cofactorChoices (actualBins z xi) m
          let S := cofactorScale z xi m
          z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → U ≤ (sourceW z)^K →
          (∀ q ∈ Q,∀ p ∈ P,
            Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent) →
          (∀ q ∈ Q,∀ p ∈ P,∀ u ∈ Uset,
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
          weightedWitness P Q Uset
            (actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
              (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma (sigma/16) h/32)) ≤
            sigma*(harmonicMass P*harmonicMass Q*harmonicMass Uset) := by
  have hb : 0 < sigma/16 := by positivity
  have hb1 : sigma/16 ≤ 1 := by linarith
  obtain ⟨xi0,hxi0,hxi01,hNo⟩ := source_no_dense_cell_jb247 Clen Cparent aStar K alpha delta (sigma/16) h
    hClen hCparent ha ha1 hK halpha hd hb hb1 hh
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 : xi ≤ 1 := hxib.trans hxi01
  filter_upwards [hNo xi hxi hxib,
    source_dense_initial_cell Clen xi sigma alpha delta (sampleGamma (sigma/16) h/32)
      hClen hxi hxi1 hsigma halpha,source_span_geometry]
    with z hno hdense hspan
  intro m i j hij hmi hmj hm a
  dsimp only
  intro hRlo hRhi hUhi hparent hchild
  let R := lower (sourceW z) z xi i
  let U := lower (sourceW z) z xi j
  let theta := effectiveWidth (sourceW z) z xi
  let P := actualBins z xi i
  let Uset := actualBins z xi j
  let Q := cofactorChoices (actualBins z xi) m
  let S := cofactorScale z xi m
  let k := ∑ t,m t
  let M0 := smallModulus (sourceW z)
  have hthetaLow : xi/4 ≤ theta :=
    effectiveWidth_ge_quarter hspan.1 hspan.2.1 hxi hxi1 (hspan.2.2 xi hxi hxi1)
  have hthetaHigh : theta ≤ xi := effectiveWidth_le hspan.1 hspan.2.1 hxi
  have hWU : sourceW z ≤ U := (bin_source_bounds hspan.1 hspan.2.1 hxi j).1
  by_contra hn
  have hBad := lt_of_not_ge hn
  obtain ⟨cell,q0,hq0,hCsize,hCount,hCQ,hdata⟩ := hdense.2 R theta U theta hRlo hWU
    hthetaLow hthetaHigh hthetaLow hthetaHigh m a hm hBad
  let C := initialCell Q a S xi k M0 cell
  have hq0Q : q0 ∈ Q := hCQ hq0
  have hq0data := hdata q0 hq0
  have hInfl := (actual_source_cofactor_inflation hspan.1 hspan.2.1 hxi Clen m hm q0 hq0Q).2
  have hCsq : ∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S := by
    intro q hq
    exact ⟨(hdata q hq).2.1,(actual_cofactor_effective_range hspan.1 hspan.2.1 hxi m q (hCQ hq)).2⟩
  have hCvalue : ∀ q ∈ C,(q : ℝ) ≤ cellUpper S xi cell ∧
      cellUpper S xi cell ≤ (1+xi)*(q : ℝ) := fun q hq =>
    ⟨(hdata q hq).2.2.1,(hdata q hq).2.2.2.1⟩
  have hCP : ∀ q ∈ C,∀ p ∈ P,q.Coprime p :=
    fun q hq => actual_excluded_bin_coprime hspan.1 hspan.2.1 hxi m i hmi q (hCQ hq)
  have hCU : ∀ q ∈ C,∀ u ∈ Uset,q.Coprime u :=
    fun q hq => actual_excluded_bin_coprime hspan.1 hspan.2.1 hxi m j hmj q (hCQ hq)
  have hpU : ∀ p ∈ P,∀ u ∈ Uset,p.Coprime u :=
    actual_distinct_bins_coprime hspan.1 hspan.2.1 hxi i j hij
  have hsmall : ∀ q ∈ C,∀ p ∈ P,∀ t : ℕ,t.Prime →
      (t : ℝ) ≤ sourceW z → (p*q).Coprime t :=
    fun q hq p hp => actual_parent_small_coprime hspan.1 hspan.2.1 hxi m q (hCQ hq) i p hp
  have hcong : ∀ q ∈ C,Int.ModEq (M0 : ℤ) (q : ℤ) (q0 : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit q0 a : ℤ) :=
    fun q hq => (hdata q hq).2.2.2.2
  exact hno R theta U theta (cellUpper S xi cell) S C q0 (cofactorHit q0 a) a
    hRlo hRhi hWU hUhi hthetaLow hthetaHigh hthetaLow hthetaHigh hq0 hq0data.1 hInfl
    hCsq hCvalue hpU hCP hCU hsmall (fun q hq => hchild q (hCQ hq))
    (hparent q0 hq0Q) hcong hCsize hCount

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LiteralSourceList
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
namespace ErdosInverseBoxHeight
open ErdosInverseAlignment ErdosInversePrimeBin

theorem uniform_literal_source_list (C eta α c : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ Sq R p q xi : ℝ, ∀ a : ℕ → ℤ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ Sq/q → Sq/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^α ≤ R → R ≤ z^((1:ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      (sourceRationalList (primeBin R xi) a Sq R (sourceZ z) c).card ≤ ⌈2/c^2⌉₊ := by
  have hbin := uniform_source_prime_bin_list (C:=3) heta hα (by norm_num) hc
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [uniform_box_height C hC,source_B_bounds,hbin,hL] with z hH hB hbin hL
  refine ⟨hH.1,?_⟩
  intro Sq R p q xi a hp hq hpq hSqratio hinfl hRlo hRhi hxi hxi1
  have hqSq : q ≤ Sq := (one_le_div hq).mp hSqratio
  have hSq : 0 ≤ Sq := hq.le.trans hqSq
  have hR : 0 ≤ R := (Real.rpow_nonneg (by linarith [hH.1] : 0 ≤ z) α).trans hRlo
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hqz : q ≤ z^2 := source_cofactor_le_square hL hp hq.le hpq
  have hheight := hH.2 Sq R (sourceB z) xi q hSq hR hB.2.1 hB.2.2
    hxi0 hxi1 hq hqz hinfl hRhi
  apply hbin.2 R xi Sq (sourceZ z) a hRlo hxi hxi1 hSq
  norm_num at hheight ⊢
  exact hheight

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualBoxList
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
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseAlignment
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem actual_box_list_card (Clen aStar alpha xi cp : ℝ) (hClen : 0 ≤ Clen)
    (ha : 0 < aStar) (halpha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hcp : 0 < cp) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
      (i j : Fin (binCount (sourceW z) z xi)),
      ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
      ∀ a : ℕ → ℕ,
      z^alpha ≤ lower (sourceW z) z xi i →
      lower (sourceW z) z xi i ≤ z^((1 : ℝ)/100) →
      (∀ q ∈ cofactorChoices (actualBins z xi) m,∀ p ∈ actualBins z xi i,∀ u ∈ actualBins z xi j,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
      (sourceRationalList (actualBins z xi i) (fun p => (a p : ℤ)) (cofactorScale z xi m)
        (lower (sourceW z) z xi i) (sourceZ z) cp).card ≤ ⌈2/cp^2⌉₊ := by
  filter_upwards [uniform_literal_source_list Clen (xi/4) alpha cp hClen (by positivity) halpha hcp,
    source_span_geometry,source_cofactor_cell_data Clen xi 1 hClen hxi hxi1 zero_lt_one,
    source_sample_population xi 1 0 hxi hxi1,sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hlist hspan hcof hpop hW
  intro m i j hm a hRlo hRhi hchild
  have hthetaLow := effectiveWidth_ge_quarter hspan.1 hspan.2.1 hxi hxi1 (hspan.2.2 xi hxi hxi1)
  have hthetaHigh := effectiveWidth_le hspan.1 hspan.2.1 hxi
  have hP := (hpop (lower (sourceW z) z xi i) (effectiveWidth (sourceW z) z xi)
    (bin_source_bounds hspan.1 hspan.2.1 hxi i).1 hthetaLow hthetaHigh).1
  have hU := (hpop (lower (sourceW z) z xi j) (effectiveWidth (sourceW z) z xi)
    (bin_source_bounds hspan.1 hspan.2.1 hxi j).1 hthetaLow hthetaHigh).1
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hP
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hU
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (hcof m hm).2.1
  have hqpos := ((hcof m hm).2.2.2 q hq).1
  have hpp := (bin_prime_in_source hspan.1 hspan.2.1 hxi i hp).1
  have hup := (bin_prime_in_source hspan.1 hspan.2.1 hxi j hu).1
  have hpq := parent_product_le_of_child_log (sourceY z) p q u (sourceW z) aStar
    hpp.pos hqpos hup.one_lt.le (by linarith) ha (hchild q hq p hp u hu)
  have hrange := actual_source_cofactor_inflation hspan.1 hspan.2.1 hxi Clen m hm q hq
  exact hlist.2 (cofactorScale z xi m) (lower (sourceW z) z xi i) (p : ℝ) (q : ℝ)
    (effectiveWidth (sourceW z) z xi) (fun p => (a p : ℤ))
    (by exact_mod_cast hpp.one_lt.le) (by exact_mod_cast hqpos) hpq hrange.1 hrange.2
    hRlo hRhi hthetaLow (hthetaHigh.trans hxi1)

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualSourceInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem mem_actualInverseException (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) (p q u : ℕ) :
    ((p,q),u) ∈ actualInverseException Y small a delta V0 S R Z cp P Q U ↔
      p ∈ P ∧ q ∈ Q ∧ u ∈ U ∧ Nonstructured P (fun p => (a p : ℤ)) S R Z cp p q ∧
        WitnessingBadEdge Y small a delta V0 p q u := by
  constructor
  · intro hmem
    obtain ⟨hprod,hWitness⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hpq,hu⟩ := Finset.mem_product.mp hprod
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact ⟨hp,hq,hu,hWitness.1,hWitness.2⟩
  · rintro ⟨hp,hq,hu,hNon,hBad⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hu⟩,⟨hNon,hBad⟩⟩

theorem actual_exception_weight (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) :
    (∑ t ∈ actualInverseException Y small a delta V0 S R Z cp P Q U,tripleWeight t) =
      weightedWitness P Q U (actualWitness Y small a delta V0 P S R Z cp) := rfl

theorem normalized_exception_bound (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (h : weightedWitness P Q U witness ≤ sigma*(harmonicMass P*harmonicMass Q*harmonicMass U)) :
    weightedWitness P Q U witness/(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma := by
  have hm : 0 ≤ harmonicMass P*harmonicMass Q*harmonicMass U :=
    mul_nonneg (mul_nonneg (harmonicMass_nonneg P) (harmonicMass_nonneg Q)) (harmonicMass_nonneg U)
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm,div_zero]
    exact hsigma
  · exact (div_le_iff₀ hm).mpr h

theorem structured_outside_actual_exception (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) (p q u : ℕ)
    (hp : p ∈ P) (hq : q ∈ Q) (hu : u ∈ U)
    (hout : ((p,q),u) ∉ actualInverseException Y small a delta V0 S R Z cp P Q U)
    (hbad : WitnessingBadEdge Y small a delta V0 p q u) :
    ∃ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
      aligns (fun p => (a p : ℤ)) t p ∧
        ((t.den*badPrimeProduct (fun p => (a p : ℤ)) t q : ℕ) : ℝ) ≤ R*Z^10 := by
  by_contra hn
  exact hout ((mem_actualInverseException Y small a delta V0 S R Z cp P Q U p q u).mpr
    ⟨hp,hq,hu,hn,hbad⟩)

end ErdosInverseBoxApplication

end

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable

theorem source_inverse_conclusion_of_bounds (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp sigma : ℝ) (F : ℕ) (P Q U : Finset ℕ)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hsigma : 0 ≤ sigma)
    (hlist : (sourceRationalList P (fun p => (a p : ℤ)) S R Z cp).card ≤ F)
    (hweight : weightedWitness P Q U (actualWitness Y small a delta V0 P S R Z cp) ≤
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U)) :
    SourceInverseConclusion Y small a delta V0 S R Z cp sigma F P Q U := by
  refine ⟨hlist,?_,?_,?_⟩
  · intro t ht
    exact (mem_sourceRationalList P (fun p => (a p : ℤ)) hS hR t).mp ht
  · rw [actual_exception_weight]
    exact normalized_exception_bound P Q U _ sigma hsigma hweight
  · exact fun p hp q hq u hu => structured_outside_actual_exception Y small a delta V0 S R Z cp
      P Q U p q u hp hq hu

end ErdosInverseBoxApplication

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem exists_inverse_sample_length (aStar : ℝ) (ha : 0 < aStar) :
    ∃ h : ℕ,12 < aStar*(h : ℝ)/2 := by
  obtain ⟨h,hh⟩ := exists_nat_gt (24/aStar)
  refine ⟨h,?_⟩
  have hm := (div_lt_iff₀ ha).mp hh
  nlinarith

theorem actual_source_inverse_jb247_oai (Clen Cparent aStar K alpha delta sigma : ℝ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,
        ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
          (i j : Fin (binCount (sourceW z) z xi)),
          i ≠ j → m i = 0 → m j = 0 →
          ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
          ∀ a : ℕ → ℕ,
          let R := lower (sourceW z) z xi i
          let U := lower (sourceW z) z xi j
          let P := actualBins z xi i
          let Uset := actualBins z xi j
          let Q := cofactorChoices (actualBins z xi) m
          let S := cofactorScale z xi m
          z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → U ≤ (sourceW z)^K →
          (∀ q ∈ Q,∀ p ∈ P,
            Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent) →
          (∀ q ∈ Q,∀ p ∈ P,∀ u ∈ Uset,
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
          SourceInverseConclusion (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
            (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) S R (sourceZ z) cp sigma F P Q Uset := by
  obtain ⟨h,hh⟩ := exists_inverse_sample_length aStar ha
  let cp := sampleGamma (sigma/16) h/32
  have hcp : 0 < cp := div_pos (sampleGamma_pos (sigma/16) h (by positivity)) (by norm_num)
  obtain ⟨xi0,hxi0,hxi01,hWeight⟩ := actual_box_nonstructured_harmonic Clen Cparent aStar K alpha delta sigma h
    hClen hCparent ha ha1 hK halpha hd hsigma hsigma1 hh
  refine ⟨cp,hcp,⌈2/cp^2⌉₊,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hWeight xi hxi hxib,actual_box_list_card Clen aStar alpha xi cp hClen ha halpha hxi hxi1 hcp,
    source_span_geometry] with z hweight hlist hspan
  intro m i j hij hmi hmj hm a
  dsimp only
  intro hRlo hRhi hUhi hparent hchild
  have hw := hweight m i j hij hmi hmj hm a hRlo hRhi hUhi hparent hchild
  have hl := hlist m i j hm a hRlo hRhi hchild
  apply source_inverse_conclusion_of_bounds
  · exact (actual_cofactorScale_pos hspan.1 hspan.2.1 hxi m).le
  · exact (endpoint_pos hspan.1 i.1).le
  · exact hsigma.le
  · exact hl
  · exact hw

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247_oai := @OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247_oai
