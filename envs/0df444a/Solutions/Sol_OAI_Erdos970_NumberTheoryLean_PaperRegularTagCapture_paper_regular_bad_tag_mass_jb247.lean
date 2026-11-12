-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:18.340956+00:00
-- url     : https://prove2.me/submissions/f505eba9-0ceb-4c79-aba6-de92662416ef

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
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RetainedOccupationLimit_retained_original_occupation_limit_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

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
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceProductsBasics.availablePrimes_closed
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FactorDividesAbscissa
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

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

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualCollisionBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

end ErdosInversePrimeBin

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CorrectSearchTags
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBinOwners

open _root_.Erdos970.Set
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem mem_ownerCandidates {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (a : ℕ → ℤ) (q : ℚ) :
    q ∈ ownerCandidates Y w Cs eta R xi a ↔ eligible Y w Cs q ∧
      (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ) := by
  have hw0 : 0 < w := by linarith
  rw [ownerCandidates,mem_sourceRationalList _ _ (by positivity) (Real.rpow_nonneg hw0.le Cs)]
  have he : Y*w^2*w^Cs = Y*w^(Cs+2) := by
    rw [Real.rpow_add hw0,Real.rpow_ofNat]
    ring
  simp only [one_pow,mul_one,he,eligible]
  tauto

theorem chooseOwner_mem (C : Finset ℚ) {q : ℚ} (h : chooseOwner C = some q) : q ∈ C := by
  by_cases hC : C.Nonempty
  · rw [chooseOwner,dite_eq_left hC] at h
    have he := Option.some.inj h
    exact he ▸ Finset.min'_mem C hC
  · simp [chooseOwner,hC] at h

theorem chooseOwner_of_unique (C : Finset ℚ) (q : ℚ) (hq : q ∈ C)
    (hunique : ∀ r ∈ C,r = q) : chooseOwner C = some q := by
  have hC : C.Nonempty := ⟨q,hq⟩
  have hm := hunique (C.min' hC) (Finset.min'_mem C hC)
  simp [chooseOwner,hC,hm]

theorem actual_owner_witness {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (a : ℕ → ℤ) {q : ℚ} (ho : owner Y w Cs eta R xi a = some q) :
    eligible Y w Cs q ∧ (1-eta)*((primeBin R xi).card:ℝ) ≤
      (((primeBin R xi).filter (aligns a q)).card:ℝ) :=
  (mem_ownerCandidates hY hw a q).mp (chooseOwner_mem _ ho)

end NumberTheoryLean.ActualBinOwners

end

section

namespace NumberTheoryLean.FiniteFirstTag


theorem firstTagFrom_witness {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ)
    {t : Tag n} (ht : firstTagFrom F k ps = some t) :
    ∃ pre : List ℕ,∃ p : ℕ,∃ tail : List ℕ, ps = pre++p::tail ∧
      t.index = k+pre.length ∧ F p = some (t.bin,t.rational) ∧ ∀ q ∈ pre,F q = none := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom] at ht
  | cons p ps ih =>
    cases hp : F p with
    | none =>
      rw [firstTagFrom,hp] at ht
      obtain ⟨pre,q,tail,hps,hindex,hq,hpre⟩ := ih (k+1) ht
      refine ⟨p::pre,q,tail,?_,?_,hq,?_⟩
      · rw [List.cons_append,hps]
      · simp only [List.length_cons]
        omega
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hp
        · exact hpre r hr
    | some bq =>
      rcases bq with ⟨b,q⟩
      rw [firstTagFrom,hp] at ht
      have he : (⟨k,b,q⟩ : Tag n) = t := Option.some.inj ht
      subst t
      exact ⟨[],p,ps,rfl,by simp,hp,by simp⟩

end NumberTheoryLean.FiniteFirstTag

end

section

namespace NumberTheoryLean.OwnerUniquenessFinite
open ActualBinOwners ErdosInverseAlignment ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable

theorem common_dense_lower (P : Finset ℕ) (a : ℕ → ℤ) (q r : ℚ) (eta : ℝ)
    (hq : (1-eta)*(P.card:ℝ) ≤ ((P.filter (aligns a q)).card:ℝ))
    (hr : (1-eta)*(P.card:ℝ) ≤ ((P.filter (aligns a r)).card:ℝ)) :
    (1-2*eta)*(P.card:ℝ) ≤ ((commonAligners P a q r).card:ℝ) := by
  let A := P.filter (aligns a q)
  let B := P.filter (aligns a r)
  have hsub : A ∪ B ⊆ P := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hu := Finset.card_le_card hsub
  have hi : A ∩ B=commonAligners P a q r := by ext p; simp [A,B,commonAligners]; tauto
  have hh := Finset.card_union_add_card_inter A B
  rw [hi] at hh
  have hhr : ((A ∪ B).card:ℝ)+((commonAligners P a q r).card:ℝ)=(A.card:ℝ)+(B.card:ℝ) := by exact_mod_cast hh
  have hur : ((A ∪ B).card:ℝ) ≤ (P.card:ℝ) := by exact_mod_cast hu
  change (1-eta)*(P.card:ℝ) ≤ (A.card:ℝ) at hq
  change (1-eta)*(P.card:ℝ) ≤ (B.card:ℝ) at hr
  nlinarith

theorem eligible_determinant_height {Y w Cs : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (q r : ℚ) (hq : eligible Y w Cs q) (hr : eligible Y w Cs r) :
    ((determinant q r).natAbs:ℝ) ≤ 2*Y*w^(2*Cs+2) := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hnat : (determinant q r).natAbs ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
    simpa only [determinant,Int.natAbs_mul,Int.natAbs_natCast] using
      (Int.natAbs_sub_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ)))
  have hh : ((determinant q r).natAbs:ℝ) ≤
      (q.num.natAbs:ℝ)*(r.den:ℝ)+(r.num.natAbs:ℝ)*(q.den:ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ _ := hh
    _ ≤ (Y*w^(Cs+2))*w^Cs+(Y*w^(Cs+2))*w^Cs :=
      add_le_add (mul_le_mul hq.2 hr.1 (Nat.cast_nonneg _) (by positivity))
        (mul_le_mul hr.2 hq.1 (Nat.cast_nonneg _) (by positivity))
    _ = 2*Y*(w^(Cs+2)*w^Cs) := by ring
    _ = _ := by rw [← Real.rpow_add hw0]; congr 2; ring

theorem owner_candidates_unique {Y w Cs eta R xi C : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ)
    (hheight : 2*Y*w^(2*Cs+2) ≤ R^C)
    (hcount : C < (1-2*eta)*((primeBin R xi).card:ℝ)) :
    ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  intro q hq r hr
  by_contra hne
  have hq' := (mem_ownerCandidates hY hw a q).mp hq
  have hr' := (mem_ownerCandidates hY hw a r).mp hr
  have hd := (eligible_determinant_height hY hw q r hq'.1 hr'.1).trans hheight
  have hP : ∀ p ∈ primeBin R xi,p.Prime := fun p hp =>
    ((mem_primeBin (zero_lt_one.trans hR).le hxi p).mp hp).1
  have hlarge : ∀ p ∈ primeBin R xi,R^(1:ℝ) ≤ (p:ℝ) := by
    intro p hp
    rw [Real.rpow_one]
    exact ((mem_primeBin (zero_lt_one.trans hR).le hxi p).mp hp).2.1.le
  have hu := common_primes_power_height_bound (primeBin R xi) a hne hP hR (by norm_num : (0:ℝ)<1) hlarge hd
  rw [div_one] at hu
  exact (not_le_of_gt hcount) ((common_dense_lower (primeBin R xi) a q r eta hq'.2 hr'.2).trans hu)

theorem owner_unique_of_exp_height {Y w Cs eta R xi H : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ)
    (hheight : 2*Y*w^(2*Cs+2) ≤ Real.exp H)
    (hcount : H < (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R) :
    ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  apply owner_candidates_unique hY hw hR hxi a (C := H/Real.log R)
  · have he : R^(H/Real.log R)=Real.exp H := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hR)]
      congr 1
      field_simp [(Real.log_pos hR).ne']
    rw [he]
    exact hheight
  · exact (div_lt_iff₀ (Real.log_pos hR)).mpr hcount
end NumberTheoryLean.OwnerUniquenessFinite

end

section

namespace NumberTheoryLean.OwnerSearchBounds

theorem height_exp_square {Y w Cs : ℝ} (_hY : 0 ≤ Y) (hw : 1 ≤ w) (hCs : 0 ≤ Cs)
    (hlarge : 2*Cs+3 ≤ w) (hYup : Y ≤ Real.exp (w^2)) :
    2*Y*w^(2*Cs+2) ≤ Real.exp (2*w^2) := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hA : 0 ≤ 2*Cs+2 := by linarith
  have hlog : Real.log w ≤ w := (Real.log_le_sub_one_of_pos hw0).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hh := mul_le_mul_of_nonneg_left hlog hA
  have hbound : w^2+(2*Cs+2)*Real.log w+Real.log 2 ≤ 2*w^2 := by nlinarith
  have he : Real.exp (w^2+(2*Cs+2)*Real.log w+Real.log 2)=2*Real.exp (w^2)*w^(2*Cs+2) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hw0]
    rw [mul_comm (2*Cs+2) (Real.log w)]
    ring
  calc
    _ ≤ 2*Real.exp (w^2)*w^(2*Cs+2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hYup (by norm_num)) (Real.rpow_nonneg hw0.le _)
    _ = Real.exp (w^2+(2*Cs+2)*Real.log w+Real.log 2) := he.symm
    _ ≤ _ := Real.exp_le_exp.mpr hbound

theorem search_ge_fourth {w R : ℝ} (hw : 1 ≤ w) (hp : 4 ≤ w^((1/4:ℝ)))
    (hR : w^(w^((1/4:ℝ))) ≤ R) : w^4 ≤ R := by
  have hh := Real.rpow_le_rpow_of_exponent_le hw hp
  have hh' : w^4 ≤ w^(w^((1/4:ℝ))) := by simpa only [Real.rpow_ofNat] using hh
  exact hh'.trans hR

theorem le_fourth {w : ℝ} (hw : 1 ≤ w) : w ≤ w^4 := by
  have h2 : 1 ≤ w^2 := by nlinarith
  nlinarith [sq_nonneg (w^2-1)]

theorem quadratic_lt_scaled_fourth {beta w : ℝ} (hb : 0 < beta) (hw : 1 ≤ w)
    (hlarge : 4/beta ≤ w) : 2*w^2 < beta*w^4 := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hbw : 4 ≤ beta*w := by nlinarith [(div_le_iff₀ hb).mp hlarge]
  have hb2 : 4 ≤ beta*w^2 := by
    have hh := mul_le_mul_of_nonneg_right hbw hw0.le
    nlinarith
  have hh := mul_pos (show 0 < beta*w^2-2 by linarith) (sq_pos_of_pos hw0)
  nlinarith
end NumberTheoryLean.OwnerSearchBounds

end

section

namespace NumberTheoryLean.UniformSearchOwner
open _root_.Filter _root_.Erdos970.Filter ActualBinOwners OwnerSearchBounds OwnerUniquenessFinite
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem uniform_search_owner_unique {Cs eta theta : ℝ} (hCs : 0 ≤ Cs)
    (heta : eta < 1/2) (htheta : 0 < theta) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ Y R xi : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      w^(w^((1/4:ℝ))) ≤ R → theta ≤ xi → xi ≤ 1 → ∀ a : ℕ → ℤ,
      ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  let beta : ℝ := (1-2*eta)*theta/4
  have hcoef : 0 < 1-2*eta := by linarith
  have hbeta : 0 < beta := by dsimp [beta] <;> positivity
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_prime_bin_count htheta)
  have hquarter : ∀ᶠ w : ℝ in atTop,4 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 4
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop R₀,
    eventually_ge_atTop (2*Cs+3),eventually_ge_atTop (4/beta),hquarter] with w hw2 hwR hwCs hwBeta hwPow
  refine ⟨hw2,?_⟩
  intro Y R xi hY hYup hsearch hxi hxi1 a
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hfour := search_ge_fourth hw1 hwPow hsearch
  have hwR' : w ≤ R := (le_fourth hw1).trans hfour
  have hcount := hR₀ R (hwR.trans hwR')
  have hR1 : 1 < R := by linarith [hcount.1]
  have hR0 : 0 < R := zero_lt_one.trans hR1
  have hlog : 0 < Real.log R := Real.log_pos hR1
  have hc := (hcount.2 xi hxi hxi1).1
  have hcm : xi*R/4 ≤ ((primeBin R xi).card:ℝ)*Real.log R := by
    have hh := (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mp hc
    nlinarith
  have hlower : beta*R ≤ (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R := by
    calc
      beta*R=(1-2*eta)*(theta*R/4) := by dsimp [beta] <;> ring
      _ ≤ (1-2*eta)*(xi*R/4) := by gcongr
      _ ≤ (1-2*eta)*(((primeBin R xi).card:ℝ)*Real.log R) :=
        mul_le_mul_of_nonneg_left hcm hcoef.le
      _ = _ := by ring
  have hsize : 2*w^2 < (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R :=
    (quadratic_lt_scaled_fourth hbeta hw1 hwBeta).trans_le
      ((mul_le_mul_of_nonneg_left hfour hbeta.le).trans hlower)
  exact owner_unique_of_exp_height hY (by linarith) hR1 (htheta.le.trans hxi) a
    (height_exp_square hY hw1 hCs hwCs hYup) hsize

theorem owner_eq_of_unique {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w) (a : ℕ → ℤ)
    (hu : ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r)
    (q : ℚ) (he : eligible Y w Cs q)
    (hd : (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ)) :
    owner Y w Cs eta R xi a=some q := by
  have hq := (mem_ownerCandidates hY hw a q).mpr ⟨he,hd⟩
  exact chooseOwner_of_unique _ q hq (fun r hr => hu r hr q hq)
end NumberTheoryLean.UniformSearchOwner

end

section

namespace NumberTheoryLean.ActualSourceTags

open _root_.Erdos970.Set
open ActualBinOwners FiniteFirstTag PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem candidate_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q)) :
    b = label p ∧ p ∈ primeBin (lower (label p)) (width (label p)) ∧
      searchBin w (lower (label p)) ∧ owner Y w Cs eta (lower (label p)) (width (label p)) a = some q ∧
      aligns a q p := by
  by_cases hgood : p ∈ primeBin (lower (label p)) (width (label p)) ∧ searchBin w (lower (label p))
  · rw [tagCandidate,ite_eq_left hgood] at ht
    cases ho : owner Y w Cs eta (lower (label p)) (width (label p)) a with
    | none => simp [ho] at ht
    | some r =>
      rw [ho] at ht
      dsimp only at ht
      by_cases ha : aligns a r p
      · rw [ite_eq_left ha] at ht
        have hh := Prod.mk.inj (Option.some.inj ht)
        rcases hh with ⟨hb,hq⟩
        subst r
        exact ⟨hb.symm,hgood.1,hgood.2,rfl,ha⟩
      · simp [ha] at ht
  · simp [tagCandidate,hgood] at ht

theorem candidate_of_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) (q : ℚ)
    (hp : p ∈ primeBin (lower (label p)) (width (label p))) (hs : searchBin w (lower (label p)))
    (ho : owner Y w Cs eta (lower (label p)) (width (label p)) a = some q) (ha : aligns a q p) :
    tagCandidate Y w Cs eta lower width label a p = some (label p,q) := by
  simp only [tagCandidate,hp,hs,and_self,ite_true, if_true,ho,ha]

theorem sourceTag_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {t : Tag n}
    (ht : sourceTag Y w Cs eta lower width label a ps = some t) :
    ∃ pre : List ℕ,∃ p : ℕ,∃ tail : List ℕ, ps = pre++p::tail ∧ t.index = pre.length ∧
      t.bin = label p ∧ p ∈ primeBin (lower (label p)) (width (label p)) ∧
      searchBin w (lower (label p)) ∧ owner Y w Cs eta (lower (label p)) (width (label p)) a = some t.rational ∧
      aligns a t.rational p ∧ ∀ q ∈ pre,tagCandidate Y w Cs eta lower width label a q = none := by
  obtain ⟨pre,p,tail,hps,hindex,hp,hpre⟩ := firstTagFrom_witness
    (tagCandidate Y w Cs eta lower width label a) 0 ps ht
  have hc := candidate_witness Y w Cs eta lower width label a p hp
  exact ⟨pre,p,tail,hps,by simpa only [zero_add] using hindex,hc.1,hc.2.1,hc.2.2.1,
    hc.2.2.2.1,hc.2.2.2.2,hpre⟩

end NumberTheoryLean.ActualSourceTags

end

section

namespace NumberTheoryLean.CorrectSearchTags
open _root_.Filter _root_.Erdos970.Filter ActualBinOwners ActualSourceTags UniformSearchOwner PrimeBinRepresentatives
open ErdosInverseAlignment ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable

theorem searchBin_lower {w R : ℝ} (hw : 1 < w) (hR : 0 < R) (hs : searchBin w R) :
    w^(w^((1/4:ℝ))) ≤ R := by
  have hlog : 0 < Real.log w := Real.log_pos hw
  have hh := (le_div_iff₀ hlog).mp hs
  calc
    _ = Real.exp (Real.log w*w^((1/4:ℝ))) := Real.rpow_def_of_pos (zero_lt_one.trans hw) _
    _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by nlinarith only [hh])
    _ = R := Real.exp_log hR

theorem uniform_correct_owner {Cs eta theta : ℝ} (hCs : 0 ≤ Cs)
    (heta : eta < 1/2) (htheta : 0 < theta) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ Y R xi : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      0 < R → searchBin w R → theta ≤ xi → xi ≤ 1 → ∀ (a : ℕ → ℤ) (q : ℚ),
      eligible Y w Cs q →
      (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ) →
      owner Y w Cs eta R xi a=some q := by
  filter_upwards [uniform_search_owner_unique hCs heta htheta] with w hw
  refine ⟨hw.1,?_⟩
  intro Y R xi hY hYup hR hs hxi hxi1 a q he hd
  have hw1 : 1 < w := by linarith [hw.1]
  exact owner_eq_of_unique hY hw1 a
    (hw.2 Y R xi hY hYup (searchBin_lower hw1 hR hs) hxi hxi1 a) q he hd

end NumberTheoryLean.CorrectSearchTags

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

theorem common_width_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hspan : (1+xi)*w ≤ z) :
    0 < effectiveWidth w z xi ∧ xi/4 ≤ effectiveWidth w z xi ∧ effectiveWidth w z xi ≤ xi ∧
      ∀ i : Fin (binCount w z xi),width w z xi i = effectiveWidth w z xi := by
  have hl : Real.log (1+xi) ≤ Real.log (z/w) :=
    Real.log_le_log (by linarith : 0 < 1+xi) ((le_div_iff₀ hw).mpr hspan)
  exact ⟨effectiveWidth_pos hw hwz hxi,effectiveWidth_ge_quarter hw hwz hxi hxi1 hl,
    effectiveWidth_le hw hwz hxi,fun _ => rfl⟩

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

theorem sourceW_pow_sourceB {L : ℝ} (hW : 1 < sourceW L) :
    (sourceW L)^(sourceB L)=Real.exp L := by
  rw [sourceB,Real.rpow_def_of_pos (by linarith : 0 < sourceW L)]
  congr 1
  field_simp [ne_of_gt (Real.log_pos hW)]

end NumberTheoryLean.JacobsthalSourceScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiniteWeightedChoiceBox
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FiniteWeightedChoiceBox

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}

theorem mass_factorizes (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ) :
    boxMass P W=∏ i,∑ x ∈ P i,W i x := (Finset.prod_univ_sum P W).symm

omit [DecidableEq ι] in
theorem weight_nonnegative (W : ∀ i,α i → ℝ) (hW : ∀ i x,0 ≤ W i x) (f : ∀ i,α i) :
    0 ≤ pointWeight W f := Finset.prod_nonneg (fun i _ => hW i (f i))

theorem restricted_eq (P : ∀ i,Finset (α i)) (S : Finset ι) (E : ∀ i,α i → Prop) :
    restrictedPoints P S E=points (fun i => if i ∈ S then (P i).filter (E i) else P i) := by
  ext f
  simp only [restrictedPoints,points,Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hp,he⟩ i
    by_cases hi : i ∈ S
    · simpa only [ite_eq_left hi,Finset.mem_filter] using And.intro (hp i) (he i hi)
    · simpa only [ite_eq_right hi] using hp i
  · intro hf
    constructor
    · intro i
      have hh := hf i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at hh; exact (Finset.mem_filter.mp hh).1
      · rwa [ite_eq_right hi] at hh
    · intro i hi
      have hh := hf i
      rw [ite_eq_left hi] at hh
      exact (Finset.mem_filter.mp hh).2

theorem restriction_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (S : Finset ι) (E : ∀ i,α i → Prop) (c : ℝ)
    (hcoord : ∀ i ∈ S,(∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ restrictedPoints P S E,pointWeight W f) ≤ c^S.card*boxMass P W := by
  rw [restricted_eq]
  change boxMass (fun i => if i ∈ S then (P i).filter (E i) else P i) W ≤ _
  rw [mass_factorizes,mass_factorizes]
  calc
    _ ≤ ∏ i,(if i ∈ S then c else 1)*(∑ x ∈ P i,W i x) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun x _ => hW i x)
      · intro i _
        by_cases hi : i ∈ S
        · simp only [ite_eq_left hi]
          exact hcoord i hi
        · simp only [ite_eq_right hi,one_mul,le_refl]
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_ite_mem_eq]; simp

theorem coordinate_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (E : ∀ i,α i → Prop) (i : ι) (c : ℝ)
    (hi : (∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ (points P).filter (fun f => E i (f i)),pointWeight W f) ≤ c*boxMass P W := by
  have hh := restriction_mass_bound P W hW {i} E c (fun j hj => by
    have he : j=i := Finset.mem_singleton.mp hj
    subst j
    exact hi)
  simpa only [restrictedPoints,Finset.mem_singleton,forall_eq,Finset.card_singleton,pow_one] using hh

theorem union_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (S : Finset ι) (E : ∀ i,α i → Prop) (c : ℝ)
    (hcoord : ∀ i ∈ S,(∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ (points P).filter (fun f => ∃ i ∈ S,E i (f i)),pointWeight W f) ≤
      (S.card:ℝ)*c*boxMass P W := by
  have hu : (∑ f ∈ (points P).filter (fun f => ∃ i ∈ S,E i (f i)),pointWeight W f) ≤
      ∑ i ∈ S,∑ f ∈ (points P).filter (fun f => E i (f i)),pointWeight W f := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f _hf
    by_cases he : ∃ i ∈ S,E i (f i)
    · rw [ite_eq_left he]
      obtain ⟨i,hi,hei⟩ := he
      have hh := Finset.single_le_sum (s := S) (f := fun j => if E j (f j) then pointWeight W f else 0)
        (fun j _ => by split_ifs; exact weight_nonnegative W hW f; rfl) hi
      simpa only [ite_eq_left hei] using hh
    · rw [ite_eq_right he]
      exact Finset.sum_nonneg (fun j _ => by split_ifs; exact weight_nonnegative W hW f; rfl)
  apply hu.trans
  calc
    _ ≤ ∑ _i ∈ S,c*boxMass P W := Finset.sum_le_sum (fun i hi => coordinate_mass_bound P W hW E i c (hcoord i hi))
    _ = _ := by simp [mul_assoc]
end NumberTheoryLean.FiniteWeightedChoiceBox


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualFirstTagExistence
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PaperOwnerHeight
open _root_.Filter JacobsthalSourceScale


theorem sourceW_square_two_L : ∀ᶠ L : ℝ in atTop,2*L ≤ (sourceW L)^2 := by
  have hh := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (s := 1) (by norm_num)).bound
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with L hsmall hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hl : 0 < Real.log L := Real.log_pos hL
  have h4 : (Real.log L)^4 ≤ L/2 := by
    simpa only [Real.rpow_ofNat,Real.rpow_one,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hl.le 4),abs_of_pos hL0,one_div,mul_comm,div_eq_mul_inv,one_mul] using hsmall
  rw [sourceW,div_pow,← pow_mul]
  apply (le_div_iff₀ (pow_pos hl 4)).mpr
  have hm := mul_le_mul_of_nonneg_left h4 hL0.le
  nlinarith

theorem literal_source_floor_height : ∀ᶠ z : ℝ in atTop,
    ((⌊z^2/(Real.log z)^2⌋₊:ℕ):ℝ) ≤ Real.exp ((sourceW (Real.log z))^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually sourceW_square_two_L,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with z hW hz hlog
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hy : ((⌊z^2/(Real.log z)^2⌋₊:ℕ):ℝ) ≤ z^2 := by
    exact (Nat.floor_le (div_nonneg (sq_nonneg z) (sq_nonneg (Real.log z)))).trans
      (div_le_self (sq_nonneg z) (by nlinarith : 1 ≤ (Real.log z)^2))
  have he : z^2=Real.exp (2*Real.log z) := by
    rw [show 2*Real.log z=Real.log (z^2) by rw [Real.log_pow]; norm_num]
    exact (Real.exp_log (sq_pos_of_pos hz0)).symm
  exact hy.trans (he.trans_le (Real.exp_le_exp.mpr hW))
end NumberTheoryLean.PaperOwnerHeight



namespace NumberTheoryLean.PaperBinOwners
open _root_.Filter JacobsthalSourceScale PaperOwnerHeight CorrectSearchTags UniformSearchOwner ActualBinOwners
open ActualSourceTags LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinMaps
open ErdosInverseAlignment ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem paper_bin_span {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,2 ≤ sourceW (Real.log z) ∧ sourceW (Real.log z) < z ∧
      (1+xi)*sourceW (Real.log z) ≤ z := by
  have hsmall := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).bound (by norm_num : (0:ℝ)<1/2)
  filter_upwards [Real.tendsto_log_atTop.eventually sourceW_bounds_eventually,
    (sourceW_tendsto.comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
    hsmall,eventually_gt_atTop (1:ℝ)] with z hW hw2 hlog hz
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlog0 : 0 < Real.log z := Real.log_pos hz
  have hlog' : Real.log z ≤ z/2 := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hlog0,abs_of_pos hz0,
      one_div,mul_comm,div_eq_mul_inv,one_mul] using hlog
  have hspan : (1+xi)*sourceW (Real.log z) ≤ z := by
    have hh := mul_le_mul_of_nonneg_right (show 1+xi ≤ 2 by linarith) (by linarith : 0 ≤ sourceW (Real.log z))
    nlinarith [hW.2.2]
  have hzw : sourceW (Real.log z) < z := by
    have hh := mul_pos hxi (show 0 < sourceW (Real.log z) by linarith)
    nlinarith
  exact ⟨hw2,hzw,hspan⟩

end NumberTheoryLean.PaperBinOwners



namespace ErdosTagEvent
open NumberTheoryLean FiniteFirstTag ActualSourceTags


theorem firstTagFrom_none_iff {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ) :
    firstTagFrom F k ps=none ↔ ∀ p ∈ ps,F p=none := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom]
  | cons p ps ih =>
    cases he : F p with
    | none => simp [firstTagFrom,he,ih]
    | some bq => rcases bq with ⟨b,q⟩; simp [firstTagFrom,he]

theorem firstTag_exists_of_candidate {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ)
    {p : ℕ} {bq : Fin n × ℚ} (hp : p ∈ ps) (hc : F p=some bq) :
    ∃ t,firstTag F ps=some t := by
  cases ht : firstTag F ps with
  | none =>
    have hnone := (firstTagFrom_none_iff F 0 ps).mp ht p hp
    rw [hc] at hnone
    contradiction
  | some t => exact ⟨t,rfl⟩

theorem sourceTag_exists_of_candidate {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {p : ℕ} {b : Fin n} {q : ℚ}
    (hp : p ∈ ps) (hc : tagCandidate Y w Cs eta lower width label a p=some (b,q)) :
    ∃ t,sourceTag Y w Cs eta lower width label a ps=some t :=
  firstTag_exists_of_candidate _ ps hp hc

end ErdosTagEvent


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeChoiceCoordinateMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeBinAlignmentMass
open ErdosInversePrimeBin


theorem mass_nonnegative (P : Finset ℕ) : 0 ≤ mass P :=
  Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem subset_mass_bounds {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) (P : Finset ℕ)
    (hP : P ⊆ primeBin R xi) :
    (P.card:ℝ)/((1+xi)*R) ≤ mass P ∧ mass P ≤ (P.card:ℝ)/R := by
  have hden : 0 < (1+xi)*R := by positivity
  constructor
  · calc
      _ = ∑ _p ∈ P,((1+xi)*R)⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun p hp => by
        obtain ⟨hpp,_hlo,hhi⟩ := (mem_primeBin hR.le hxi p).mp (hP hp)
        simpa only [one_div] using (one_div_le_one_div_of_le (by exact_mod_cast hpp.pos : (0:ℝ)<p) hhi))
  · calc
      _ ≤ ∑ _p ∈ P,R⁻¹ := Finset.sum_le_sum (fun p hp => by
        obtain ⟨_hpp,hlo,_hhi⟩ := (mem_primeBin hR.le hxi p).mp (hP hp)
        simpa only [one_div] using (one_div_le_one_div_of_le hR hlo.le))
      _ = _ := by simp [div_eq_mul_inv]

theorem non_nearfull_mass {R xi eta : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) (heta : 0 ≤ eta)
    (A : Finset ℕ) (hA : A ⊆ primeBin R xi)
    (hcard : (A.card:ℝ) ≤ (1-eta)*((primeBin R xi).card:ℝ)) :
    mass A ≤ (1-eta/(1+xi))*mass (primeBin R xi) := by
  let P := primeBin R xi
  let C := P \ A
  have hden : 0 < (1+xi)*R := by positivity
  have hcardC : eta*(P.card:ℝ) ≤ (C.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card hA
    have hhr : (C.card:ℝ)+(A.card:ℝ)=(P.card:ℝ) := by exact_mod_cast hh
    change (A.card:ℝ) ≤ (1-eta)*(P.card:ℝ) at hcard
    nlinarith
  have hPmass := (subset_mass_bounds hR hxi P (fun _ h => h)).2
  have hCmass := (subset_mass_bounds hR hxi C Finset.sdiff_subset).1
  have hsum : mass C=mass P-mass A := Finset.sum_sdiff_eq_sub hA
  have hbound : eta/(1+xi)*mass P ≤ mass C := by
    calc
      _ ≤ eta/(1+xi)*((P.card:ℝ)/R) :=
        mul_le_mul_of_nonneg_left hPmass (div_nonneg heta (by positivity))
      _ = (eta*(P.card:ℝ))/((1+xi)*R) := by
        field_simp [hR.ne',(by positivity : (1+xi:ℝ) ≠ 0)]
      _ ≤ (C.card:ℝ)/((1+xi)*R) := div_le_div_of_nonneg_right hcardC hden.le
      _ ≤ _ := hCmass
  rw [hsum] at hbound
  linarith
end NumberTheoryLean.PrimeBinAlignmentMass



namespace NumberTheoryLean.PrimeChoiceAlignmentDecay
open PrimeBinAlignmentMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem search_power_bound {w c eta xi : ℝ} (hw : 1 < w) (_hc : 0 < c)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (n : ℕ) (hcount : c*Real.log w ≤ (n:ℝ)) :
    (1-eta/(1+xi))^n ≤ w^(-(c*eta/2)) := by
  have hden : 0 < 1+xi := by linarith
  have hquot : eta/(1+xi) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hbase : 0 ≤ 1-eta/(1+xi) := by linarith
  have hq : eta/2 ≤ eta/(1+xi) := div_le_div_of_nonneg_left heta0.le hden (by linarith)
  have hsmall : 1-eta/(1+xi) ≤ Real.exp (-(eta/2)) :=
    (sub_le_sub_left hq 1).trans (Real.one_sub_le_exp_neg (eta/2))
  have hpow := pow_le_pow_left₀ hbase hsmall n
  apply hpow.trans
  rw [← Real.exp_nat_mul,Real.rpow_def_of_pos (zero_lt_one.trans hw)]
  apply Real.exp_le_exp.mpr
  nlinarith

end NumberTheoryLean.PrimeChoiceAlignmentDecay



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SingletonSubsetMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SingletonSubsetMass
open PrimeBinAlignmentMass

attribute [local instance] Classical.propDecidable

theorem subsetWeight_nonnegative (s : Finset ℕ) : 0 ≤ subsetWeight s :=
  Finset.prod_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem singleton_total_mass (P : Finset ℕ) :
    (∑ s ∈ P.powersetCard 1,subsetWeight s)=mass P := by
  rw [Finset.powersetCard_one,Finset.sum_map]
  simp [subsetWeight,mass]

theorem all_filter_powerset (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop) :
    (P.powersetCard k).filter (fun s => ∀ p ∈ s,E p)=(P.filter E).powersetCard k := by
  ext s
  simp only [Finset.mem_filter,Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub,hcard⟩,he⟩
    refine ⟨?_,hcard⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hsub hp,he p hp⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨⟨?_,hcard⟩,?_⟩
    · intro p hp
      exact (Finset.mem_filter.mp (hsub hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (hsub hp)).2

theorem singleton_all_mass (P : Finset ℕ) (E : ℕ → Prop) :
    (∑ s ∈ (P.powersetCard 1).filter (fun s => ∀ p ∈ s,E p),subsetWeight s)=mass (P.filter E) := by
  rw [all_filter_powerset,singleton_total_mass]

theorem singleton_some_mass (P A : Finset ℕ) (hA : A ⊆ P) :
    (∑ s ∈ (P.powersetCard 1).filter (fun s => ∃ p ∈ s,p ∈ A),subsetWeight s)=mass A := by
  calc
    _ = ∑ s ∈ A.powersetCard 1,subsetWeight s := by
      apply Finset.sum_congr
      · ext s
        simp only [Finset.mem_filter,Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_hSP,hcard⟩,hex⟩
          obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp hcard
          simp only [Finset.mem_singleton,exists_eq_left] at hex
          exact ⟨Finset.singleton_subset_iff.mpr hex,by simp⟩
        · rintro ⟨hSA,hcard⟩
          obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp hcard
          have hpA := hSA (by simp : p ∈ ({p} : Finset ℕ))
          exact ⟨⟨fun q hq => hA (hSA hq),by simp⟩,p,by simp,hpA⟩
      · intro s _hs
        rfl
    _ = _ := singleton_total_mass A

end NumberTheoryLean.SingletonSubsetMass


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_WrongOwnerBoxMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WrongOwnerBinMass
open PrimeBinAlignmentMass ActualBinOwners OwnerUniquenessFinite OwnerSearchBounds
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem wrongOwnerPrimes_none (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (ho : owner Y w Cs eta R xi a=none) : wrongOwnerPrimes Y w Cs eta R xi a q=∅ := by
  ext p
  simp [wrongOwnerPrimes,ho]

theorem wrongOwnerPrimes_self (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (ho : owner Y w Cs eta R xi a=some q) : wrongOwnerPrimes Y w Cs eta R xi a q=∅ := by
  ext p
  simp [wrongOwnerPrimes,ho]

theorem wrongOwnerPrimes_eq_common (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q r : ℚ)
    (ho : owner Y w Cs eta R xi a=some r) (hne : r ≠ q) :
    wrongOwnerPrimes Y w Cs eta R xi a q=commonAligners (primeBin R xi) a q r := by
  ext p
  simp [wrongOwnerPrimes,ho,hne,commonAligners]

theorem wrong_owner_mass_bound {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hCs : 0 ≤ Cs) (hwlarge : 2*Cs+3 ≤ w) (hYup : Y ≤ Real.exp (w^2))
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ) (q : ℚ) (hq : eligible Y w Cs q) :
    mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤ 2*w^2/(R*Real.log R) := by
  have hRp0 : 0 < R := zero_lt_one.trans hR
  have hlog0 : 0 < Real.log R := Real.log_pos hR
  have hnon : 0 ≤ 2*w^2/(R*Real.log R) := by positivity
  cases ho : owner Y w Cs eta R xi a with
  | none => simpa only [wrongOwnerPrimes_none Y w Cs eta R xi a q ho,mass,Finset.sum_empty] using hnon
  | some r =>
    by_cases he : r=q
    · subst r
      simpa only [wrongOwnerPrimes_self Y w Cs eta R xi a q ho,mass,Finset.sum_empty] using hnon
    · rw [wrongOwnerPrimes_eq_common Y w Cs eta R xi a q r ho he]
      have hr := (actual_owner_witness hY hw a ho).1
      have hd := (eligible_determinant_height hY hw q r hq hr).trans
        (height_exp_square hY hw.le hCs hwlarge hYup)
      have hRp : 0 < R := zero_lt_one.trans hR
      have hlog : 0 < Real.log R := Real.log_pos hR
      have hheight : ((determinant q r).natAbs:ℝ) ≤ R^(2*w^2/Real.log R) := by
        have hh : R^(2*w^2/Real.log R)=Real.exp (2*w^2) := by
          rw [Real.rpow_def_of_pos hRp]
          congr 1
          field_simp [hlog.ne']
        rwa [hh]
      have hp : ∀ p ∈ primeBin R xi,p.Prime := fun p hp => ((mem_primeBin hRp.le hxi p).mp hp).1
      have hlarge : ∀ p ∈ primeBin R xi,R^(1:ℝ) ≤ (p:ℝ) := by
        intro p hp
        rw [Real.rpow_one]
        exact ((mem_primeBin hRp.le hxi p).mp hp).2.1.le
      have hc := common_primes_power_height_bound (primeBin R xi) a (Ne.symm he) hp hR
        (by norm_num : (0:ℝ)<1) hlarge hheight
      rw [div_one] at hc
      calc
        _ ≤ ((commonAligners (primeBin R xi) a q r).card:ℝ)/R :=
          (subset_mass_bounds hRp hxi _ (Finset.filter_subset _ _)).2
        _ ≤ (2*w^2/Real.log R)/R := div_le_div_of_nonneg_right hc hRp.le
        _ = _ := by rw [div_div,mul_comm (Real.log R) R]
end NumberTheoryLean.WrongOwnerBinMass



namespace NumberTheoryLean.WrongOwnerFraction
open _root_.Filter PrimeBinAlignmentMass WrongOwnerBinMass ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment


theorem uniform_bin_mass_lower {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,theta ≤ xi → xi ≤ 1 →
      theta/(8*Real.log R) ≤ mass (primeBin R xi) := by
  filter_upwards [uniform_prime_bin_count htheta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hRp : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have hxi0 : 0 ≤ xi := htheta.le.trans hxi
  have hden : 0 < (1+xi)*R := by positivity
  have hc : theta/8 ≤ xi/(4*(1+xi)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*(1+xi))).mpr
    have hh := mul_le_mul_of_nonneg_left hxi1 htheta.le
    nlinarith
  have hm := (div_le_div_of_nonneg_right (hR.2 xi hxi hxi1).1 hden.le).trans
    (subset_mass_bounds hRp hxi0 (primeBin R xi) (fun _ h => h)).1
  calc
    _ = (theta/8)/Real.log R := by rw [div_div]
    _ ≤ (xi/(4*(1+xi)))/Real.log R := div_le_div_of_nonneg_right hc hlog.le
    _ = (xi*R/(4*Real.log R))/((1+xi)*R) := by
      field_simp [hRp.ne',hlog.ne',(by positivity : (1+xi:ℝ) ≠ 0)]
    _ ≤ _ := hm

theorem uniform_wrong_owner_fraction {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ Y w Cs eta xi : ℝ,
      0 ≤ Y → 1 < w → 0 ≤ Cs → 2*Cs+3 ≤ w → Y ≤ Real.exp (w^2) →
      theta ≤ xi → xi ≤ 1 → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤
        (16*w^2/(theta*R))*mass (primeBin R xi) := by
  filter_upwards [uniform_bin_mass_lower htheta] with R hR
  refine ⟨hR.1,?_⟩
  intro Y w Cs eta xi hY hw hCs hwlarge hYup hxi hxi1 a q hq
  have hRp : 0 < R := by linarith [hR.1]
  have hR1 : 1 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos hR1
  have habs := wrong_owner_mass_bound (eta := eta) hY hw hCs hwlarge hYup hR1 (htheta.le.trans hxi) a q hq
  have hm := mul_le_mul_of_nonneg_left (hR.2 xi hxi hxi1)
    (show 0 ≤ 16*w^2/(theta*R) by positivity)
  have he : (16*w^2/(theta*R))*(theta/(8*Real.log R))=2*w^2/(R*Real.log R) := by
    field_simp [hRp.ne',hlog.ne',htheta.ne']
    norm_num
  rw [he] at hm
  exact habs.trans hm
end NumberTheoryLean.WrongOwnerFraction



namespace NumberTheoryLean.WrongOwnerSearchTail
open _root_.Filter PrimeBinAlignmentMass WrongOwnerBinMass WrongOwnerFraction ActualBinOwners OwnerSearchBounds
open ErdosInversePrimeBin


theorem search_fraction_factor {theta A : ℝ} (_htheta : 0 < theta) (_hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ R : ℝ,w^(w^((1/4:ℝ))) ≤ R →
      16*w^2/(theta*R) ≤ w^(-A) := by
  have hquarter : ∀ᶠ w : ℝ in atTop,A+3 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop (A+3)
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (16/theta),hquarter] with w hw2 hwC hwPow
  intro R hR
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hRa : w^(A+3) ≤ R := (Real.rpow_le_rpow_of_exponent_le hw1 hwPow).trans hR
  have hden : 0 < w^(A+3) := Real.rpow_pos_of_pos hw0 _
  have hRp : 0 < R := hden.trans_le hRa
  have hnum : (16/theta)*w^2 ≤ w^3 := by
    have hh := mul_le_mul_of_nonneg_right hwC (sq_nonneg w)
    nlinarith
  calc
    _ = ((16/theta)*w^2)/R := by simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
    _ ≤ w^3/R := div_le_div_of_nonneg_right hnum hRp.le
    _ ≤ w^3/w^(A+3) := div_le_div_of_nonneg_left (pow_nonneg hw0.le 3) hden hRa
    _ = w^(-A) := by
      rw [show w^3=w^(3:ℝ) by norm_num,← Real.rpow_sub hw0]
      congr 1
      ring

theorem actual_wrong_search_mass {Cs theta A : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ Y R xi eta : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      w^(w^((1/4:ℝ))) ≤ R → theta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤ w^(-A)*mass (primeBin R xi) := by
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_wrong_owner_fraction htheta)
  have hquarter : ∀ᶠ w : ℝ in atTop,4 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 4
  filter_upwards [search_fraction_factor htheta hA,eventually_ge_atTop (2:ℝ),eventually_ge_atTop R₀,
    eventually_ge_atTop (2*Cs+3),hquarter] with w hfactor hw2 hwR hwCs hwPow
  intro Y R xi eta hY hYup hsearch hxi hxi1 a q hq
  have hw1 : 1 ≤ w := by linarith
  have hRlarge : R₀ ≤ R := hwR.trans ((le_fourth hw1).trans (search_ge_fourth hw1 hwPow hsearch))
  have hh := (hR₀ R hRlarge).2 Y w Cs eta xi hY (by linarith) hCs hwCs hYup hxi hxi1 a q hq
  exact hh.trans (mul_le_mul_of_nonneg_right (hfactor R hsearch) (mass_nonnegative _))
end NumberTheoryLean.WrongOwnerSearchTail



namespace NumberTheoryLean.WrongOwnerBoxMass
open _root_.Filter PrimeChoiceAlignmentDecay
open PrimeBinAlignmentMass WrongOwnerBinMass WrongOwnerSearchTail ActualBinOwners
open ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem logarithmic_positions_le_w (Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,2*Clen*Real.log w ≤ w := by
  have hD : 0 < 2*Clen+1 := by linarith
  have hh := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).bound
    (show 0 < 1/(2*Clen+1) by positivity)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with w hsmall hw
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hlog0 : 0 < Real.log w := Real.log_pos hw
  have hs : Real.log w ≤ w/(2*Clen+1) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hlog0,abs_of_pos hw0,
      one_div,mul_comm,div_eq_mul_inv,one_mul] using hsmall
  have hm := (le_div_iff₀ hD).mp hs
  nlinarith

end NumberTheoryLean.WrongOwnerBoxMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SubsetPrimeBoxMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetPrimeBoxMass
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass PrimeBinAlignmentMass
open WrongOwnerSearchTail WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem no_nearfull_subset_mass {n : ℕ} (R : Fin n → ℝ) (xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hxi : 0 ≤ xi) (heta : 0 ≤ eta) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ restrictedPoints (fun i => (primeBin (R i) xi).powersetCard (mult i)) S
      (fun _ s => ∀ p ∈ s,aligns a q p),pointWeight (fun _ => subsetWeight) f) ≤
      (1-eta/(1+xi))^S.card*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  apply restriction_mass_bound
  · intro i s
    exact subsetWeight_nonnegative s
  · intro i hi
    rw [hsingle i hi,singleton_total_mass]
    have he := singleton_all_mass (primeBin (R i) xi) (aligns a q)
    calc
      _ = mass ((primeBin (R i) xi).filter (aligns a q)) := by
        convert! he using 1
        all_goals try with_reducible_and_instances rfl
        exact Finset.sum_congr (by ext s; simp only [Finset.mem_filter]) (fun _ _ => rfl)
      _ ≤ _ := non_nearfull_mass (hR i) hxi heta _ (Finset.filter_subset _ _) (hd i hi)

theorem no_nearfull_subset_power {n : ℕ} (R : Fin n → ℝ) (w c xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hw : 1 < w) (hc : 0 < c) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (hcount : c*Real.log w ≤ (S.card:ℝ)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ restrictedPoints (fun i => (primeBin (R i) xi).powersetCard (mult i)) S
      (fun _ s => ∀ p ∈ s,aligns a q p),pointWeight (fun _ => subsetWeight) f) ≤
      w^(-(c*eta/2))*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  have hmass : 0 ≤ boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i)) (fun _ => subsetWeight) := by
    exact Finset.sum_nonneg (fun f _ => weight_nonnegative _ (fun _ => subsetWeight_nonnegative) f)
  exact (no_nearfull_subset_mass R xi eta mult hR hxi0 heta0.le S hsingle a q hd).trans
    (mul_le_mul_of_nonneg_right (PrimeChoiceAlignmentDecay.search_power_bound hw hc heta0 heta1 hxi0 hxi1 S.card hcount) hmass)

theorem wrong_owner_subset_mass {Cs theta A : ℝ} (hCs : 0 ≤ Cs) (htheta : 0 < theta) (hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ) (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (points (fun i => (primeBin (R i) xi).powersetCard (mult i))).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        pointWeight (fun _ => subsetWeight) f) ≤
      (S.card:ℝ)*w^(-A)*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  filter_upwards [actual_wrong_search_mass hCs htheta hA] with w hw
  intro Y xi eta hY hYup hxi hxi1 n R mult S hsingle hsearch a q hq
  have hh := union_mass_bound (fun i => (primeBin (R i) xi).powersetCard (mult i))
    (fun _ => subsetWeight) (fun _ s => subsetWeight_nonnegative s) S
    (fun i s => ∃ p ∈ s,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q) (w^(-A)) (by
      intro i hi
      rw [hsingle i hi,singleton_total_mass]
      have he := singleton_some_mass (primeBin (R i) xi) (wrongOwnerPrimes Y w Cs eta (R i) xi a q)
        (Finset.filter_subset _ _)
      calc
        _ = mass (wrongOwnerPrimes Y w Cs eta (R i) xi a q) := by
          convert! he using 1
          all_goals try with_reducible_and_instances rfl
          exact Finset.sum_congr (by ext s; simp only [Finset.mem_filter]) (fun _ _ => rfl)
        _ ≤ _ := hw Y (R i) xi eta hY hYup (hsearch i hi) hxi hxi1 a q hq)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  exact Finset.sum_congr (by ext f; simp only [Finset.mem_filter]) (fun _ _ => rfl)
end NumberTheoryLean.SubsetPrimeBoxMass


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_TwoSingletonBins
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetBoxBookkeeping
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass SubsetPrimeBoxMass
open WrongOwnerBoxMass WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem subset_box_original_weight {n : ℕ} (f : Fin n → Finset ℕ) :
    pointWeight (fun _ => subsetWeight) f=(((∏ i,∏ p ∈ f i,p):ℕ):ℝ)⁻¹ := by
  simp [pointWeight,subsetWeight,Finset.prod_inv_distrib]

theorem search_card_le_multiplicity {n : ℕ} (mult : Fin n → ℕ) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) : S.card ≤ ∑ i,mult i := by
  calc
    S.card = ∑ i ∈ S,mult i := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsingle i hi).symm
    _ ≤ ∑ i,mult i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

theorem length_bounded_subset_wrong_mass {Cs theta A Clen : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta B : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      Real.log B ≤ 2*Real.log w → ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ),
      ((∑ i,mult i):ℝ) ≤ Clen*Real.log B → ∀ (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (points (fun i => (primeBin (R i) xi).powersetCard (mult i))).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        pointWeight (fun _ => subsetWeight) f) ≤
      w^(-A)*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  filter_upwards [wrong_owner_subset_mass hCs htheta (show 0 < A+1 by linarith),
    logarithmic_positions_le_w Clen hC,eventually_gt_atTop (1:ℝ)] with w hw hlength hw1
  intro Y xi eta B hY hYup hxi hxi1 hB n R mult hm S hsingle hsearch a q hq
  have hraw := hw Y xi eta hY hYup hxi hxi1 n R mult S hsingle hsearch a q hq
  have hcard : (S.card:ℝ) ≤ w := by
    have hsmr : (S.card:ℝ) ≤ ∑ i,(mult i:ℝ) := by exact_mod_cast search_card_le_multiplicity mult S hsingle
    have hmul := mul_le_mul_of_nonneg_left hB hC
    nlinarith
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hmul := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hw0.le (-(A+1)))
  have he : w*w^(-(A+1))=w^(-A) := by
    calc
      _ = w^(1:ℝ)*w^(-(A+1)) := by rw [Real.rpow_one]
      _ = w^((1:ℝ)+(-(A+1))) := (Real.rpow_add hw0 _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hmul
  have hmass : 0 ≤ boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i)) (fun _ => subsetWeight) :=
    Finset.sum_nonneg (fun f _ => weight_nonnegative _ (fun _ => subsetWeight_nonnegative) f)
  exact hraw.trans (mul_le_mul_of_nonneg_right hmul hmass)
end NumberTheoryLean.SubsetBoxBookkeeping



namespace NumberTheoryLean.CanonicalSubsetBox
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass SubsetPrimeBoxMass SubsetBoxBookkeeping
open WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin ErdosInverseAlignment ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

theorem canonical_points {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) :
    points (fun i => (P i).powersetCard (mult i))=selections P mult := by
  ext f
  simp only [points,selections,Fintype.mem_piFinset]

theorem canonical_weight {n : ℕ} (f : Fin n → Finset ℕ) :
    pointWeight (fun _ => subsetWeight) f=(selectionProduct f:ℝ)⁻¹ := subset_box_original_weight f

theorem selectionMass_eq_weighted {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) :
    selectionMass P mult=boxMass (fun i => (P i).powersetCard (mult i)) (fun _ => subsetWeight) := by
  rw [selectionMass,boxMass,canonical_points]
  apply Finset.sum_congr rfl
  intro f _hf
  exact (canonical_weight f).symm

theorem canonical_no_nearfull_mass {n : ℕ} (R : Fin n → ℝ) (w c xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hw : 1 < w) (hc : 0 < c) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (hcount : c*Real.log w ≤ (S.card:ℝ)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ (selections (fun i => primeBin (R i) xi) mult).filter
      (fun f => ∀ i ∈ S,∀ p ∈ f i,aligns a q p),(selectionProduct f:ℝ)⁻¹) ≤
      w^(-(c*eta/2))*selectionMass (fun i => primeBin (R i) xi) mult := by
  have hh := no_nearfull_subset_power R w c xi eta mult hR hw hc hxi0 hxi1 heta0 heta1 S hsingle hcount a q hd
  rw [← selectionMass_eq_weighted] at hh
  simp only [restrictedPoints,canonical_points,canonical_weight] at hh
  exact hh

theorem canonical_wrong_mass {Cs theta A Clen : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta B : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      Real.log B ≤ 2*Real.log w → ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ),
      ((∑ i,mult i):ℝ) ≤ Clen*Real.log B → ∀ (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (selections (fun i => primeBin (R i) xi) mult).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        (selectionProduct f:ℝ)⁻¹) ≤
      w^(-A)*selectionMass (fun i => primeBin (R i) xi) mult := by
  filter_upwards [length_bounded_subset_wrong_mass hCs htheta hA hC] with w hw
  intro Y xi eta B hY hYup hxi hxi1 hcomp n R mult hlen S hsingle hsearch a q hq
  have hh := hw Y xi eta B hY hYup hxi hxi1 hcomp n R mult hlen S hsingle hsearch a q hq
  rw [← selectionMass_eq_weighted] at hh
  simp only [canonical_points,canonical_weight] at hh
  exact hh
end NumberTheoryLean.CanonicalSubsetBox



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PaperTagEventInclusion
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open WrongOwnerBinMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem nonnearfull_card_lt (eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (hn : ¬nearFull eta R xi a q) :
    (((primeBin R xi).filter (aligns a q)).card:ℝ) < (1-eta)*((primeBin R xi).card:ℝ) :=
  lt_of_not_ge hn

end ErdosTagEvent



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
open NumberTheoryLean FinitePathGeometry PrimeTiltGeometry PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem valid_half {i : Side} {s : ℝ} (hs : Valid i s) : (1:ℝ)/2 ≤ s := by
  cases i <;> dsimp [Valid] at hs <;> linarith

theorem child_gap_third {w ell S : ℝ} {z : Node} {p : ℕ}
    (hell : 0 ≤ ell) (hs : Valid z.side z.ratio)
    (hp : p ∈ nodeChildren w ell S z) : z.gap ≤ 3*(step w z p).gap := by
  have hx := child_exponent_positive hell hp
  have ht := valid_half (child_valid hs hp)
  change (1:ℝ)/2 ≤ z.gap/primeExponent w p-1 at ht
  have hh : (3:ℝ)/2 ≤ z.gap/primeExponent w p := by linarith
  have hm := (le_div_iff₀ hx).mp hh
  change z.gap ≤ 3*(z.gap-primeExponent w p)
  linarith

theorem initial_gap_le_search_power (w ell S : ℝ) (P : ℕ → Bool) (z : Node)
    (ps : List ℕ) (hell : 0 ≤ ell) (hs : Valid z.side z.ratio)
    (ha : allowed w ell S z ps) :
    z.gap ≤ (3:ℝ)^(selectedCount P ps)*((terminal w z ps).gap+remainderSum w P ps) := by
  induction ps generalizing z with
  | nil => simp [selectedCount,remainderSum]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (allowed_cons w ell S z p ps).mp ha
    have htail := ih (step w z p) (child_valid hs hp) ht
    have hx := (child_exponent_positive hell hp).le
    have hpow : (1:ℝ) ≤ 3^(selectedCount P ps) := one_le_pow₀ (by norm_num)
    cases he : P p with
    | true =>
      have hh := child_gap_third hell hs hp
      simp [selectedCount,remainderSum,he] at *
      rw [pow_succ]
      nlinarith
    | false =>
      simp [selectedCount,remainderSum,he] at *
      change z.gap-primeExponent w p ≤ _ at htail
      nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hx]

end ErdosSearchCount



namespace ErdosSearchCount
open NumberTheoryLean PrimeHistories PrimeBinRepresentatives ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem nonsearch_exponent_bound {w top xi : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) {p : ℕ} (hp : p ∈ sourcePrimeSet w top)
    (hn : searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) p=false) :
    primeExponent w p ≤ w^((1/4:ℝ))+xi/Real.log w := by
  have hlo : leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) < w^((1/4:ℝ)) := by
    have hh : ¬searchBin w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) := by
      simpa only [searchFlag,decide_eq_false_iff_not] using hn
    exact lt_of_not_ge hh
  have hsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hmem := label_prime_membership (zero_lt_one.trans hw) htop hxi hsource.1 hsource.2
  have hupper := (bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hmem).2
  have hwidth := bin_exponent_width (w:=w)
    (R:=lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (xi:=width w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hlog : Real.log (1+width w top xi (label (zero_lt_one.trans hw) htop hxi p)) ≤ xi := by
    have hpos := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
    have he := Real.log_le_sub_one_of_pos (show 0 < 1+effectiveWidth w top xi by linarith)
    have hle := effectiveWidth_le (zero_lt_one.trans hw) htop hxi
    change Real.log (1+effectiveWidth w top xi) ≤ xi
    linarith
  have hd := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le
  change primeExponent w p ≤ rightExponent w
    (lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (width w top xi (label (zero_lt_one.trans hw) htop hxi p)) at hupper
  linarith

theorem remainderSum_le_length_mul (w : ℝ) (P : ℕ → Bool) (ps : List ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ p ∈ ps,P p=false → primeExponent w p ≤ A) :
    remainderSum w P ps ≤ (ps.length:ℝ)*A := by
  induction ps with
  | nil => simp [remainderSum]
  | cons p ps ih =>
    have ht := ih (fun q hq => hbound q (by simp [hq]))
    cases he : P p with
    | true => simp [remainderSum,he] at * <;> linarith
    | false =>
      have hp := hbound p (by simp) he
      simp [remainderSum,he] at *
      linarith

theorem source_remainder_bound {w top xi B Clen : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hlog : 1 ≤ Real.log w) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (ps : List ℕ)
    (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) (hlen : (ps.length:ℝ) ≤ Clen*Real.log B) :
    remainderSum w (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) ps ≤
      2*Clen*Real.log w*(w^((1/4:ℝ))+1) := by
  have hxdiv : xi/Real.log w ≤ 1 := (div_le_one (Real.log_pos hw)).mpr (hxi1.trans hlog)
  have hA : 0 ≤ w^((1/4:ℝ))+1 := by positivity
  have hm := remainderSum_le_length_mul w
    (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) ps hA
    (fun p hps hn => (nonsearch_exponent_bound hw htop hxi (hp p hps) hn).trans (by linarith))
  have hl : (ps.length:ℝ) ≤ 2*Clen*Real.log w := by
    have hh := mul_le_mul_of_nonneg_left hcomp hC
    nlinarith
  exact hm.trans (mul_le_mul_of_nonneg_right hl hA)

end ErdosSearchCount



namespace ErdosSearchCount
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean FinitePathGeometry PrimeHistories
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition


theorem nonsearch_budget_le (K Clen epsilon : ℝ) (hC : 0 ≤ Clen) (hepsilon : 0 < epsilon) :
    ∀ᶠ w : ℝ in atTop,K+2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ epsilon*w^((1/2:ℝ)) := by
  let eps : ℝ := epsilon/(8*(Clen+1))
  have heps : 0 < eps := by dsimp [eps] <;> positivity
  have hlog := (isLittleO_log_rpow_atTop (r := (1/4:ℝ)) (by norm_num)).bound heps
  have hpow : ∀ᶠ w : ℝ in atTop,2*K/epsilon ≤ w^((1/2:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop (2*K/epsilon)
  filter_upwards [hlog,hpow,eventually_gt_atTop (1:ℝ)] with w hlog hK hw
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hL : 0 < Real.log w := Real.log_pos hw
  have hp : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos hw0 _
  have hp1 : 1 ≤ w^((1/4:ℝ)) := Real.one_le_rpow hw.le (by norm_num)
  have hlog' : Real.log w ≤ eps*w^((1/4:ℝ)) := by
    simpa only [Real.norm_eq_abs,abs_of_pos hL,abs_of_pos hp] using hlog
  have he : w^((1/4:ℝ))*w^((1/4:ℝ))=w^((1/2:ℝ)) := by
    rw [← Real.rpow_add hw0]; norm_num
  have hb : 4*Clen*eps ≤ epsilon/2 := by
    dsimp [eps]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have hden : 0 < 8*(Clen+1) := by positivity
    field_simp
    nlinarith
  have hs : 2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ epsilon*w^((1/2:ℝ))/2 := by
    calc
      _ ≤ 4*Clen*Real.log w*w^((1/4:ℝ)) := by nlinarith [mul_nonneg (mul_nonneg hC hL.le) (sub_nonneg.mpr hp1)]
      _ ≤ 4*Clen*(eps*w^((1/4:ℝ)))*w^((1/4:ℝ)) := by gcongr
      _ = (4*Clen*eps)*w^((1/2:ℝ)) := by rw [← he]; ring
      _ ≤ (epsilon/2)*w^((1/2:ℝ)) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hw0.le _)
      _ = _ := by ring
  have hK' := (div_le_iff₀ hepsilon).mp hK
  nlinarith

theorem nonsearch_budget_small (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,K+2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ w^((1/2:ℝ)) := by
  simpa only [one_mul] using nonsearch_budget_le K Clen 1 hC (by norm_num)

theorem logarithmic_count_of_power {w R : ℝ} {k : ℕ} (hw : 1 < w)
    (hgap : w ≤ (3:ℝ)^k*R) (hsmall : R ≤ w^((1/2:ℝ))) :
    Real.log w/(2*Real.log 3) ≤ (k:ℝ) := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hpow : 0 < (3:ℝ)^k := by positivity
  have hm := hgap.trans (mul_le_mul_of_nonneg_left hsmall hpow.le)
  have hl := Real.log_le_log hw0 hm
  rw [Real.log_mul hpow.ne' (Real.rpow_pos_of_pos hw0 _).ne',Real.log_pow,
    Real.log_rpow hw0] at hl
  apply (div_le_iff₀ (show 0 < 2*Real.log 3 by positivity)).mpr
  nlinarith

theorem actual_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi ell S : ℝ) (hw : 1 < w) (htop : w < top)
      (hxi : 0 < xi),xi ≤ 1 → Real.log B ≤ 2*Real.log w → 1 ≤ ell →
      ∀ (z : Node) (ps : List ℕ),Valid z.side z.ratio → w ≤ z.gap →
      allowed w ell S z ps → (terminal w z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log B → (∀ p ∈ ps,p ∈ sourcePrimeSet w top) →
      Real.log w/(2*Real.log 3) ≤
        (searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [nonsearch_budget_small K Clen hC,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hsmall hlog
  intro top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hr := source_remainder_bound hw htop hxi hxi1 hlog hC hcomp ps hp hlen
  have hi := initial_gap_le_search_power w ell S
    (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) z ps
    (by linarith : 0 ≤ ell) hs ha
  apply logarithmic_count_of_power hw (hstart.trans hi)
  exact (add_le_add hK hr).trans hsmall

theorem searchConstant_pos : 0 < searchConstant := by unfold searchConstant; positivity

theorem actual_search_count_uniform (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi ell S : ℝ) (hw : 1 < w) (htop : w < top)
      (hxi : 0 < xi),xi ≤ 1 → Real.log B ≤ 2*Real.log w → 1 ≤ ell →
      ∀ (z : Node) (ps : List ℕ),Valid z.side z.ratio → w ≤ z.gap →
      allowed w ell S z ps → (terminal w z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log B → (∀ p ∈ ps,p ∈ sourcePrimeSet w top) →
      searchConstant*Real.log w ≤
        (searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [actual_search_count K Clen hC] with w hwcount
  intro top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hh := hwcount top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hwL : 0 ≤ Real.log w := (Real.log_pos hw).le
  apply le_trans _ hh
  unfold searchConstant
  field_simp
  nlinarith

end ErdosSearchCount



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

theorem word_search_count {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=
      ∑ b,if searchBin w (lower w top xi b) then mult b else 0 := by
  have hmem := (mem_selections _ mult f).mp hf
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [searchCount,selectedCount_eq_sum,← List.sum_toFinset _ (descendingWord_nodup f),
    descendingWord_toFinset,selectionPrimes,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b _
    calc
      _ = ∑ _p ∈ f b,if searchBin w (lower w top xi b) then (1:ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hl := selected_prime_label hw htop hxi mult f hf b hp
        simp [searchFlag,hl]
      _ = _ := by split_ifs <;> simp [(hmem b).2]
  · intro i _ j _ hij
    exact selection_disjoint _ hd f (fun b => (hmem b).1) hij

theorem word_search_count_eq_occupied {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult)
    (hone : ∀ b ∈ occupiedSearch w top xi mult,mult b=1) :
    searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=
      (occupiedSearch w top xi mult).card := by
  rw [word_search_count hw htop hxi mult f hf,occupiedSearch,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hs : searchBin w (lower w top xi b)
  · by_cases hm : 0 < mult b
    · have hh := hone b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,hm⟩)
      simp [hs,hh]
    · have hz : mult b=0 := by omega
      simp [hs,hz]
  · simp [hs]

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

theorem source_mesh_clearance_condition {w xi Clen : ℝ}
    (hw : 1 ≤ Real.log w) (hxi : 0 ≤ xi) (hC : 1 ≤ Clen) :
    2*(xi/Real.log w) ≤ 6*(2*Clen*xi) := by
  have hdiv : xi/Real.log w ≤ xi := div_le_self hxi hw
  have hprod : xi ≤ Clen*xi := by nlinarith
  linarith
end NumberTheoryLean.ActualPrefixClearance


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

theorem wordMultiplicity_count {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ)
    (hn : ps.Nodup) (b : Fin n) : wordMultiplicity lab ps b=(ps.map lab).count b := by
  have he : ps.toFinset.filter (fun p => lab p=b) = (ps.filter (fun p => lab p==b)).toFinset := by
    ext p
    simp
  rw [wordMultiplicity,wordSelection,he]
  rw [List.toFinset_card_of_nodup (hn.filter _)]
  rw [List.count,List.countP_map,List.countP_eq_length_filter]
  rfl
end NumberTheoryLean.ActualWordSelection


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

theorem regular_boxes_search_singletons {w top xi Clen B K : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) :
    ∀ mult ∈ regularBoxes hw htop hxi Clen B K z,
      ∀ b ∈ occupiedSearch w top xi mult,mult b=1 := by
  intro mult hm b hb
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd,_hlen,_hclear,_hgap,hsingle⟩ := Finset.mem_filter.mp hps
  have hn : ps.Nodup := (mem_decreasingPrefixes.mp hd).1.imp (fun h => ne_of_gt h)
  have hpos := (Finset.mem_filter.mp hb).2.2
  have hle := hsingle b (Finset.mem_filter.mp hb).2.1
  rw [wordMultiplicity_count _ ps hn] at hpos ⊢
  omega
end NumberTheoryLean.ActualRegularBoxes



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PaperMissingPrimeWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PaperMissingPrimeWindow

open _root_.Set _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open JacobsthalSourceScale MissingWindowPrimeMass ErdosPrimeInputs.PrimePrefixMass

theorem sourceW_le_sourceB_eventually : ∀ᶠ L : ℝ in atTop,sourceW L ≤ sourceB L := by
  filter_upwards [sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hW hL hlog
  have hLp : 0 < L := by linarith
  have hlogW : 0 < Real.log (sourceW L) := Real.log_pos hW.1
  have hd : Real.log (sourceW L) ≤ (Real.log L)^2 := by
    have hh := Real.log_le_log (by linarith [hW.1] : 0 < sourceW L) hW.2.2
    nlinarith
  exact div_le_div_of_nonneg_left hLp.le hlogW hd

end NumberTheoryLean.PaperMissingPrimeWindow

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PaperSubsetTagEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag WrongOwnerBinMass
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem subset_bad_tag_inclusion {Y w top Cs eta xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (a : ℕ → ℤ) (q : ℚ) (hf : f ∈ selections (globalBins w top xi) mult)
    (howner : ∀ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q →
      owner Y w Cs eta (lower w top xi b) (width w top xi b) a=some q)
    (halign : ∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p)
    (hbad : ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q) :
    (∀ b ∈ occupiedSearch w top xi mult,¬nearFull eta (lower w top xi b) (width w top xi b) a q) ∨
      ∃ b ∈ occupiedSearch w top xi mult,∃ p ∈ f b,
        p ∈ wrongOwnerPrimes Y w Cs eta (lower w top xi b) (width w top xi b) a q := by
  have hmem := (mem_selections _ mult f).mp hf
  by_cases hn : ∀ b ∈ occupiedSearch w top xi mult,
      ¬nearFull eta (lower w top xi b) (width w top xi b) a q
  · exact Or.inl hn
  · push Not at hn
    obtain ⟨b,hb,hnear⟩ := hn
    have hpos : 0 < (f b).card := by rw [(hmem b).2]; exact (Finset.mem_filter.mp hb).2.2
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hpos
    have hl := selected_prime_label hw htop hxi mult f hf b hp
    have ho := howner b hb hnear
    have hs := (Finset.mem_filter.mp hb).2.1
    have hbin := (hmem b).1 hp
    have hc : tagCandidate Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a p=some (b,q) := by
      have hh := candidate_of_witness Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a p q
        (by rw [hl]; exact hbin) (by rw [hl]; exact hs) (by rw [hl]; exact ho) (halign b hb p hp)
      simpa only [hl] using hh
    obtain ⟨t,ht⟩ := sourceTag_exists_of_candidate Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f) ((mem_descendingWord f p).mpr ⟨b,hp⟩) hc
    have hne : t.rational ≠ q := fun he => hbad ⟨t,ht,he⟩
    obtain ⟨pre,p',tail,heq,_hindex,_hbin,hp',hsearch,hor,har,_hbefore⟩ :=
      sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f) ht
    have hin : p' ∈ descendingWord f := by rw [heq]; simp
    obtain ⟨b',hin⟩ := (mem_descendingWord f p').mp hin
    have hl' := selected_prime_label hw htop hxi mult f hf b' hin
    rw [hl'] at hsearch hor hp'
    have hbpos : 0 < mult b' := by
      rw [← (hmem b').2]
      exact Finset.card_pos.mpr ⟨p',hin⟩
    have hb' : b' ∈ occupiedSearch w top xi mult := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsearch,hbpos⟩
    exact Or.inr ⟨b',hb',p',hin,Finset.mem_filter.mpr ⟨hp',halign b' hb' p' hin,t.rational,hor,hne,har⟩⟩

end ErdosSubsetWord



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FullWordHighAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetTagFailureMass
open ErdosCofactorChoices ErdosSubsetWord ErdosTagEvent ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels CanonicalSubsetBox
open WrongOwnerBinMass ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem bad_mass_le_alignment {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      ∑ f ∈ (selections (globalBins w top xi) mult).filter
        (fun f => ∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p),(selectionProduct f:ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    obtain ⟨hf,ha,hbad⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hf,ha⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem bad_mass_le_wrong {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ)
    (howner : ∀ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q →
      owner Y w Cs eta (lower w top xi b) (width w top xi b) a=some q)
    (hnear : ∃ b ∈ occupiedSearch w top xi mult,
      nearFull eta (lower w top xi b) (width w top xi b) a q) :
    badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      ∑ f ∈ (selections (globalBins w top xi) mult).filter
        (fun f => ∃ b ∈ occupiedSearch w top xi mult,∃ p ∈ f b,
          p ∈ wrongOwnerPrimes Y w Cs eta (lower w top xi b) (width w top xi b) a q),(selectionProduct f:ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    obtain ⟨hf,halign,hbad⟩ := Finset.mem_filter.mp hf
    have hh := subset_bad_tag_inclusion hw htop hxi mult f a q hf howner halign hbad
    rcases hh with hnone | hwrong
    · obtain ⟨b,hb,hn⟩ := hnear
      exact False.elim (hnone b hb hn)
    · exact Finset.mem_filter.mpr ⟨hf,hwrong⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
end NumberTheoryLean.SubsetTagFailureMass



namespace NumberTheoryLean.HardTagBoxMass
open SubsetTagFailureMass ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels PrimeBinRepresentatives
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem hardBad_subset_bad {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hsearch : Cs ≤ w^((1/4:ℝ))) (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ⊆
      badSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  intro f hf
  obtain ⟨hf,halign,hbad⟩ := Finset.mem_filter.mp hf
  refine Finset.mem_filter.mpr ⟨hf,?_,hbad⟩
  intro b hb p hp
  have hbin := ((mem_selections _ mult f).mp hf b).1 hp
  have hx := (bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hbin).1
  have hs := (Finset.mem_filter.mp hb).2.1
  change w^((1/4:ℝ)) ≤ leftExponent w (lower w top xi b) at hs
  exact halign p ((mem_descendingWord f p).mpr ⟨b,hp⟩) (hsearch.trans hs |>.trans_lt hx)

theorem hardBadMass_le_badMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hsearch : Cs ≤ w^((1/4:ℝ))) (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
      badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (hardBad_subset_bad hw htop hxi hsearch mult a q)
    (fun f _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
end NumberTheoryLean.HardTagBoxMass



namespace NumberTheoryLean.SafeAnchorSearchCount
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosCofactorChoices ErdosSubsetWord ErdosSearchCount


theorem safe_anchor_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi : ℝ) (hw : 1 < w) (htop : w < top) (hxi : 0 < xi),
      xi ≤ 1 → Real.log B ≤ 2*Real.log w → ∀ z : Node,
      Valid z.side z.ratio → Consistent z → StrongState z → z.closed=true → w^z.cutoff=top → w ≤ z.gap →
      ∀ mult : Fin (binCount w top xi) → ℕ,SafeAnchor hw htop hxi Clen B K z mult →
      (∀ b ∈ occupiedSearch w top xi mult,mult b=1) →
      searchConstant*Real.log w ≤ ((occupiedSearch w top xi mult).card:ℝ) ∧
        (∑ b,(mult b:ℝ)) ≤ Clen*Real.log B := by
  filter_upwards [actual_search_count_uniform K Clen hC] with w hcount
  intro top B xi hw htop hxi hxi1 hcomp z hs hz hstrong hclosed hcap hstart mult ha hsingle
  obtain ⟨f,hf,hlen,hsafe,hK⟩ := ha
  have ha' : SafeAnchor hw htop hxi Clen B K z mult := ⟨f,hf,hlen,hsafe,hK⟩
  have href := (anchored_choice_geometry hw htop hxi hC hcomp z mult ha' f hf).1
  have htransport := source_reference_transport hw htop z hs hz hstrong hclosed hcap (descendingWord f) href
  obtain ⟨U,_hU,hallowed⟩ := (uncapped_iff_exists_ceiling w 1 z (descendingWord f)).mp
    ((mem_uncappedPrefixes hw z (descendingWord f)).mp htransport.1)
  have hsource := word_source_membership hw htop hxi mult f hf
  have hc := hcount top B xi 1 U hw htop hxi hxi1 hcomp (by norm_num) z (descendingWord f)
    hs hstart hallowed hK hlen hsource
  rw [word_search_count_eq_occupied hw htop hxi mult f hf hsingle] at hc
  refine ⟨hc,?_⟩
  have hl : ((descendingWord f).length:ℝ)=∑ b,(mult b:ℝ) := by
    exact_mod_cast global_word_length hw htop hxi mult f hf
  rwa [← hl]
end NumberTheoryLean.SafeAnchorSearchCount



namespace NumberTheoryLean.HardTagWordFamily
open HardTagBoxMass FiniteBoxWordMass ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

private theorem finite_union_mass_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : Finset β) (T : β → Finset α) (W : α → ℝ) (hW : ∀ x,0 ≤ W x) :
    (∑ x ∈ M.biUnion T,W x) ≤ ∑ b ∈ M,∑ x ∈ T b,W x := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert b M hb ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hb]
    have he : (∑ x ∈ T b ∪ M.biUnion T,W x)+(∑ x ∈ T b ∩ M.biUnion T,W x)=
        (∑ x ∈ T b,W x)+(∑ x ∈ M.biUnion T,W x) := Finset.sum_union_inter
    have hn : 0 ≤ ∑ x ∈ T b ∩ M.biUnion T,W x := Finset.sum_nonneg (fun x _ => hW x)
    linarith

theorem hardBadWords_mass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) :
    (∑ ps ∈ hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,prefixWeight ps)=
      hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [hardBadWords,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    have hs := (Finset.mem_filter.mp hf).1
    rw [StoppedVertexHistory.prefixWeight_product,descendingWord_product (globalBins w top xi) hd f
      (fun i => ((mem_selections _ mult f).mp hs i).1)]
  · intro f hf g hg he
    exact word_injective (globalBins w top xi) hd f g
      (fun i => ((mem_selections _ mult f).mp (Finset.mem_filter.mp hf).1 i).1)
      (fun i => ((mem_selections _ mult g).mp (Finset.mem_filter.mp hg).1 i).1) he

theorem hardWordFamily_mass_le {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (a : ℕ → ℤ) :
    (∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi M Q a,prefixWeight ps) ≤
      ∑ mult ∈ M,∑ q ∈ Q mult,hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q := by
  apply (finite_union_mass_le M _ prefixWeight prefixWeight_nonneg).trans
  apply Finset.sum_le_sum
  intro mult _hm
  have hh := finite_union_mass_le (Q mult)
    (fun q => hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) prefixWeight prefixWeight_nonneg
  simpa only [hardBadWords_mass] using hh
end NumberTheoryLean.HardTagWordFamily



namespace NumberTheoryLean.SafeBoxTagRate
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry SafeAnchorSearchCount SubsetTagFailureMass CanonicalSubsetBox
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinMaps
open CorrectSearchTags UniformSearchOwner ActualBinOwners ActualSourceTags
open ErdosCofactorChoices ErdosSubsetWord ErdosTagEvent ErdosSearchCount
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem safe_box_tag_rate {K Clen Cs eta xi : ℝ} (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ w : ℝ in atTop,∀ (B top : ℝ) (hw : 1 < w) (htop : w < top),3 ≤ B →
      Real.log B ≤ 2*Real.log w → ∀ Y : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → Consistent z → z.cutoff=B → z.closed=true → w^B=top → w ≤ z.gap →
      ∀ mult : Fin (binCount w top xi) → ℕ,SafeAnchor hw htop hxi Clen B K z mult →
      (∀ b ∈ occupiedSearch w top xi mult,mult b=1) → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q ≤
        (w^(-(searchConstant*eta/2))+w^(-1:ℝ))*selectionMass (globalBins w top xi) mult := by
  have htheta : 0 < xi/4 := by positivity
  have hwrong := canonical_wrong_mass (Cs := Cs) (theta := xi/4) (A := 1) (Clen := Clen)
    hCs htheta (by norm_num) hC
  filter_upwards [safe_anchor_search_count K Clen hC,uniform_correct_owner hCs heta htheta,hwrong] with w hcount howner hwrong
  intro B top hw htop hB hcomp Y hY hYup z hi h199 hz hcut hclosed hcap hstart mult hanchor hsingle a q hq
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hspan : (1+xi)*w ≤ top := by
    have hp : w^3 ≤ top := by
      have hh := Real.rpow_le_rpow_of_exponent_le hw.le hB
      rw [hcap] at hh
      simpa only [Real.rpow_ofNat] using hh
    have hw2 : 2 ≤ w := howner.1
    have hm := mul_nonneg hw0.le (show 0 ≤ w^2-2 by nlinarith)
    nlinarith
  have hwidth := common_width_bounds hw0 htop hxi hxi1 hspan
  have hvalid : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hstrong := source_strong_state hB z hi h199 hz hcut
  have hcounts := hcount top B xi hw htop hxi hxi1 hcomp z hvalid hz hstrong hclosed
    (by rwa [hcut]) hstart mult hanchor hsingle
  let I := occupiedSearch w top xi mult
  let R := lower w top xi
  have hidentify : ∀ b ∈ I,nearFull eta (R b) (width w top xi b) a q →
      owner Y w Cs eta (R b) (width w top xi b) a=some q := by
    intro b hb hnear
    exact howner.2 Y (R b) (width w top xi b) hY hYup (endpoint_pos hw0 _)
      (Finset.mem_filter.mp hb).2.1 hwidth.2.1 (hwidth.2.2.1.trans hxi1) a q hq hnear
  have hwm := hwrong Y (effectiveWidth w top xi) eta B hY hYup hwidth.2.1
    (hwidth.2.2.1.trans hxi1) hcomp (binCount w top xi) R mult hcounts.2 I hsingle
    (fun b hb => searchBin_lower hw (endpoint_pos hw0 _) (Finset.mem_filter.mp hb).2.1) a q hq
  have hmass : 0 ≤ selectionMass (globalBins w top xi) mult :=
    Finset.sum_nonneg (fun f _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  by_cases hnone : ∀ b ∈ I,¬nearFull eta (R b) (width w top xi b) a q
  · have hno := canonical_no_nearfull_mass R w searchConstant (effectiveWidth w top xi) eta mult
      (fun b => endpoint_pos hw0 _) hw searchConstant_pos hwidth.1.le (hwidth.2.2.1.trans hxi1)
      heta0 (by linarith) I hsingle hcounts.1 a q (fun b hb => (nonnearfull_card_lt _ _ _ _ _ (hnone b hb)).le)
    have hh := (bad_mass_le_alignment (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q).trans hno
    exact hh.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.rpow_nonneg hw0.le (-1))) hmass)
  · push Not at hnone
    have hh := (bad_mass_le_wrong (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q hidentify hnone).trans hwm
    exact hh.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (Real.rpow_nonneg hw0.le (-(searchConstant*eta/2)))) hmass)
end NumberTheoryLean.SafeBoxTagRate



namespace NumberTheoryLean.RegularBadTagWords
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord ErdosCofactorChoices HardTagWordFamily HardTagBoxMass ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem regularBadWords_subset {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) :
    regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q a ⊆
      hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi
        (regularBoxes hw htop hxi Clen B K z) Q a := by
  intro ps hp
  obtain ⟨hr,q,hq,ha,hbad⟩ := Finset.mem_filter.mp hp
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
  let lab := label (zero_lt_one.trans hw) htop hxi
  have hrec := wordSelection_recovers lab ps hd.1
  apply Finset.mem_biUnion.mpr
  refine ⟨wordMultiplicity lab ps,Finset.mem_image.mpr ⟨ps,hr,rfl⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q,hq,Finset.mem_image.mpr ⟨wordSelection lab ps,?_,hrec⟩⟩
  apply Finset.mem_filter.mpr
  refine ⟨wordSelection_mem hw htop hxi ps hd.2,?_⟩
  simpa only [hrec] using (show (∀ p ∈ ps,Cs < primeExponent w p → aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi) lab a ps=some t ∧ t.rational=q from ⟨ha,hbad⟩)

theorem regularBadWords_mass_le {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) :
    (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q a,prefixWeight ps) ≤
      ∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi
        (regularBoxes hw htop hxi Clen B K z) Q a,prefixWeight ps :=
  Finset.sum_le_sum_of_subset_of_nonneg (regularBadWords_subset hw htop hxi Clen B K z Q a)
    (fun ps _ _ => prefixWeight_nonneg ps)
end NumberTheoryLean.RegularBadTagWords



namespace NumberTheoryLean.GlobalSafeTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open SafeSubsetBoxGeometry SafeBoxTagRate ActualSafeBoxMass SubsetTagFailureMass CanonicalSubsetBox
open LogarithmicBinScale ActualBinOwners ErdosSubsetWord ErdosSearchCount

attribute [local instance] Classical.propDecidable

private theorem finite_candidate_sum {β : Type*} (M : Finset β) (Q : β → Finset ℚ)
    (H : ℕ) (r : ℝ) (hr : 0 ≤ r) (F : β → ℝ) (hF : ∀ b ∈ M,0 ≤ F b)
    (G : β → ℚ → ℝ) (hG : ∀ b ∈ M,∀ q ∈ Q b,G b q ≤ r*F b)
    (hQ : ∀ b ∈ M,(Q b).card ≤ H) :
    (∑ b ∈ M,∑ q ∈ Q b,G b q) ≤ (H:ℝ)*r*(∑ b ∈ M,F b) := by
  calc
    _ ≤ ∑ b ∈ M,∑ _q ∈ Q b,r*F b := Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun q hq => hG b hb q hq))
    _ = ∑ b ∈ M,((Q b).card:ℝ)*(r*F b) := by simp
    _ ≤ ∑ b ∈ M,(H:ℝ)*(r*F b) := Finset.sum_le_sum (fun b hb =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ b hb) (mul_nonneg hr (hF b hb)))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring

theorem global_bad_tag_mass_small {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ (B w top : ℝ) (hw : 1 < w) (htop : w < top),
      B₀ ≤ B → w₀ ≤ w → Real.log B ≤ 2*Real.log w → ∀ Y : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      ∀ (z : Node) (a : ℕ → ℤ),z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top → w ≤ z.gap →
      ∀ (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen B K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch w top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) → (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y w Cs q) →
      B^2*(∑ mult ∈ M,∑ q ∈ Q mult,badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) ≤ epsilon := by
  obtain ⟨C,B₀,wbox,hCpos,hB₀,hwbox,hboxes⟩ := uniform_safe_box_mass K hK
  have hd : 0 < searchConstant*eta/2 := by have hc := searchConstant_pos; positivity
  have hrate : Tendsto (fun w : ℝ => (H:ℝ)*C*(w^(-(searchConstant*eta/2))+w^(-1:ℝ))) atTop (nhds 0) := by
    have hh := ((tendsto_rpow_neg_atTop hd).add (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1))).const_mul ((H:ℝ)*C)
    simpa only [zero_add,mul_zero] using hh
  have hsmall : ∀ᶠ w : ℝ in atTop,(H:ℝ)*C*(w^(-(searchConstant*eta/2))+w^(-1:ℝ)) ≤ epsilon :=
    ((tendsto_order.mp hrate).2 epsilon hepsilon).mono (fun _ h => h.le)
  have htag := safe_box_tag_rate (K := K) (Clen := Clen) (Cs := Cs) (eta := eta) (xi := xi) hC hCs heta0 heta hxi hxi1
  obtain ⟨w₁,hw₁⟩ := eventually_atTop.mp (htag.and (hsmall.and (eventually_ge_atTop wbox)))
  refine ⟨B₀,max 2 w₁,hB₀,by have hh := le_max_left (2:ℝ) w₁; linarith,?_⟩
  intro B w top hw htop hB hW hcomp Y hY hYup z a hi h199 h23 hz hcut hclosed hcap hstart M Q hanchor hsingle hcard helig
  have hgood := hw₁ w ((le_max_right _ _).trans hW)
  have hB3 := hB₀.trans hB
  let r := w^(-(searchConstant*eta/2))+w^(-1:ℝ)
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hr : 0 ≤ r := add_nonneg (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg hw0.le _)
  have hm := finite_candidate_sum M Q H r hr (selectionMass (globalBins w top xi))
    (fun mult _ => Finset.sum_nonneg (fun f _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    (fun mult q => badMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q)
    (fun mult hmult q hq => hgood.1 B top hw htop hB3 hcomp Y hY hYup z hi h199 hz hcut hclosed hcap hstart
      mult (hanchor mult hmult) (hsingle mult hmult) a q (helig mult hmult q hq)) hcard
  have hbox := hboxes B w top hB hgood.2.2 hw htop xi Clen hxi hC hcomp hDelta z hi h199 h23 hz hcut hclosed hcap M hanchor
  calc
    _ ≤ B^2*((H:ℝ)*r*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult)) := mul_le_mul_of_nonneg_left hm (sq_nonneg B)
    _ = (H:ℝ)*r*(B^2*(∑ mult ∈ M,selectionMass (globalBins w top xi) mult)) := by ring
    _ ≤ (H:ℝ)*r*C := mul_le_mul_of_nonneg_left hbox (mul_nonneg (Nat.cast_nonneg _) hr)
    _ = (H:ℝ)*C*r := by ring
    _ ≤ epsilon := hgood.2.1
end NumberTheoryLean.GlobalSafeTagCapture



namespace NumberTheoryLean.PaperSafeTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open JacobsthalSourceScale PaperMissingPrimeWindow PaperOwnerHeight PaperBinOwners
open SafeSubsetBoxGeometry GlobalSafeTagCapture HardTagBoxMass ActualBinOwners
open LogarithmicBinScale ErdosSubsetWord

attribute [local instance] Classical.propDecidable

theorem paper_safe_hard_tag_capture {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ (M : Finset (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ))
        (Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen (sourceB (Real.log top)) K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) →
      (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ mult ∈ M,∑ q ∈ Q mult,hardBadMass (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q) ≤ epsilon := by
  obtain ⟨B₀,w₀,_hB₀,_hw₀,hbound⟩ := global_bad_tag_mass_small hK hC hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hsearch : ∀ᶠ top : ℝ in atTop,Cs ≤ (sourceW (Real.log top))^((1/4:ℝ)) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp hwT).eventually_ge_atTop Cs
  filter_upwards [paper_bin_span hxi hxi1,Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually sourceW_le_sourceB_eventually,literal_source_floor_height,
    hwT.eventually_ge_atTop w₀,hBT.eventually_ge_atTop B₀,eventually_gt_atTop (1:ℝ),hsearch]
    with top hspan hscale hWB hheight hwBound hBBound htop1 hsearch
  have hw : 1 < sourceW (Real.log top) := by linarith [hspan.1]
  refine ⟨hw,hspan.2.1,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  have hYup : (Y:ℝ) ≤ Real.exp ((sourceW (Real.log top))^2) :=
    (show (Y:ℝ) ≤ (⌊top^2/(Real.log top)^2⌋₊:ℕ) by exact_mod_cast hY).trans hheight
  have hcap : (sourceW (Real.log top))^(sourceB (Real.log top))=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  have hgap := (source_node_bounds hscale.2.1 z hi h199 h23 hz hcut).2.2.1
  have hstart := hWB.trans hgap
  have hh := hbound (sourceB (Real.log top)) (sourceW (Real.log top)) top hw hspan.2.1 hBBound hwBound
    hscale.2.2.2.2 Y (Nat.cast_nonneg Y) hYup z a hi h199 h23 hz hcut hclosed hcap hstart M Q hanchors hsingle hcard helig
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro mult _hm
  apply Finset.sum_le_sum
  intro q _hq
  exact hardBadMass_le_badMass hw hspan.2.1 hxi hsearch mult a q
end NumberTheoryLean.PaperSafeTagCapture



namespace NumberTheoryLean.PaperSafeWordCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open JacobsthalSourceScale SafeSubsetBoxGeometry HardTagWordFamily ActualBinOwners
open LogarithmicBinScale ErdosSubsetWord PaperSafeTagCapture

attribute [local instance] Classical.propDecidable

theorem paper_safe_hard_word_capture {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 0 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ (M : Finset (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ))
        (Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ),
      (∀ mult ∈ M,SafeAnchor hw htop hxi Clen (sourceB (Real.log top)) K z mult) →
      (∀ mult ∈ M,∀ b ∈ occupiedSearch (sourceW (Real.log top)) top xi mult,mult b=1) →
      (∀ mult ∈ M,(Q mult).card ≤ H) →
      (∀ mult ∈ M,∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ hardWordFamily (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi M Q a,ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  filter_upwards [paper_safe_hard_tag_capture hK hC hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon] with top htopData
  obtain ⟨hw,htop,hbound⟩ := htopData
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  have hh := hbound Y hY z a hi h199 h23 hz hcut hclosed M Q hanchors hsingle hcard helig
  exact (mul_le_mul_of_nonneg_left (hardWordFamily_mass_le (Y := Y) (Cs := Cs) (eta := eta)
    hw htop hxi M Q a) (sq_nonneg (sourceB (Real.log top)))).trans hh
end NumberTheoryLean.PaperSafeWordCapture



namespace NumberTheoryLean.PaperRegularTagCapture
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open JacobsthalSourceScale ActualRegularBoxes ActualPrefixClearance RegularBadTagWords
open PaperSafeWordCapture ActualBinOwners LogarithmicBinScale

attribute [local instance] Classical.propDecidable

theorem paper_regular_bad_tag_mass_jb247_oai {K Clen Cs eta xi : ℝ} (hK : 3 ≤ K) (hC : 1 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℤ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z,(Q mult).card ≤ H) →
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z,
        ∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen
          (sourceB (Real.log top)) K z Q a,ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  have hC0 : 0 ≤ Clen := by linarith
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [paper_safe_hard_word_capture hK hC0 hCs heta0 heta hxi hxi1 hDelta H epsilon hepsilon,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    (Real.tendsto_log_atTop.comp hwT).eventually_ge_atTop 1] with top hbound hscale hlog
  obtain ⟨hw,htop,hbound⟩ := hbound
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed Q hcard helig
  have hsmall := source_mesh_clearance_condition hlog hxi.le hC
  have hh := hbound Y hY z a hi h199 h23 hz hcut hclosed
    (regularBoxes hw htop hxi Clen (sourceB (Real.log top)) K z) Q
    (regular_boxes_anchors hw htop hxi hC0 hscale.2.2.2.2 hsmall z)
    (regular_boxes_search_singletons hw htop hxi z) hcard helig
  exact (mul_le_mul_of_nonneg_left (regularBadWords_mass_le (Y := Y) (Cs := Cs) (eta := eta)
    hw htop hxi Clen (sourceB (Real.log top)) K z Q a) (sq_nonneg _)).trans hh
end NumberTheoryLean.PaperRegularTagCapture



end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247_oai := @OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247_oai
