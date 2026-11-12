-- Prove2me | solution 1 for OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:28.034288+00:00
-- url     : https://prove2.me/submissions/771123a1-4ed8-41cb-aff2-46e150f0e533

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
import Theorems.Thm_OAI_Erdos970_ErdosInverseRefinement_source_parentSlope_mem_jb247
import Theorems.Thm_OAI_Erdos970_ErdosInverseSampleCost_source_good_sample_jb247
import Theorems.Thm_OAI_Erdos970_ErdosSourceLineBudget_uniform_original_rich_line_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformCollisionError
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosSourceCollision

theorem collision_error_bound (z R N n eta C : ℝ) (hz : 1 < z) (hR : 1 < R)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hN : z^((93 : ℝ)/100) ≤ N)
    (heta : 0 < eta) (hC : 0 ≤ C) (hL : 1 ≤ Real.log z)
    (hcount : eta*R/(4*Real.log R) ≤ n) :
    C*R/(n*(Real.log z)^6)+R/(N*(Real.log z)^6) ≤
      4*C/(eta*(Real.log z)^5)+1/z^((92 : ℝ)/100) := by
  have hz0 : 0 < z := by linarith
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hn : 0 < n := (div_pos (mul_pos heta hR0) (mul_pos (by norm_num) hlogR)).trans_le hcount
  have hNp : 0 < N := (Real.rpow_pos_of_pos hz0 _).trans_le hN
  have hLp : 0 < Real.log z := by linarith
  have hRle : R ≤ z := by
    apply hRz.trans
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (1 : ℝ)/100 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hlogs : Real.log R ≤ Real.log z := Real.log_le_log hR0 hRle
  have hprim := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogR)).mp hcount
  have hratio : R/n ≤ 4*Real.log z/eta := by
    apply (div_le_div_iff₀ hn heta).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlogs hn.le]
  have hfirst : C*R/(n*(Real.log z)^6) ≤ 4*C/(eta*(Real.log z)^5) := by
    calc
      _ = C*(R/n)/(Real.log z)^6 := by ring
      _ ≤ C*(4*Real.log z/eta)/(Real.log z)^6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) (by positivity)
      _ = _ := by field_simp
  have hpow : 0 < z^((92 : ℝ)/100) := Real.rpow_pos_of_pos hz0 _
  have hRN : R/N ≤ 1/z^((92 : ℝ)/100) := by
    apply (div_le_div_iff₀ hNp hpow).mpr
    calc
      R*z^((92 : ℝ)/100) ≤ z^((1 : ℝ)/100)*z^((92 : ℝ)/100) := mul_le_mul_of_nonneg_right hRz hpow.le
      _ = z^((93 : ℝ)/100) := by rw [← Real.rpow_add hz0];norm_num
      _ ≤ 1*N := by simpa only [one_mul] using hN
  have hden : N ≤ N*(Real.log z)^6 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL : 1 ≤ (Real.log z)^6) hNp.le
    simpa only [mul_one] using hh
  have hsecond : R/(N*(Real.log z)^6) ≤ 1/z^((92 : ℝ)/100) :=
    (div_le_div_of_nonneg_left hR0.le hNp hden).trans hRN
  exact add_le_add hfirst hsecond

end ErdosSourceCollision

end

section

open Filter
open scoped Topology
namespace ErdosSourceCollision

theorem uniform_collision_error (C eta eps : ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ 1 ≤ Real.log z ∧ ∀ R N n : ℝ,
      1 < R → R ≤ z^((1 : ℝ)/100) → z^((93 : ℝ)/100) ≤ N →
      eta*R/(4*Real.log R) ≤ n →
      C*R/(n*(Real.log z)^6)+R/(N*(Real.log z)^6) ≤ eps^2 := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (8*C/(eta*eps^2)))
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 92/100)).eventually_ge_atTop (2/eps^2)
  filter_upwards [hlog,hpow,eventually_gt_atTop (1 : ℝ)] with z hzL hzpow hz
  have hL : 1 ≤ Real.log z := (le_max_left _ _).trans hzL
  have hL0 : 0 < Real.log z := by linarith
  have hz0 : 0 < z := by linarith
  have he2 : 0 < eps^2 := sq_pos_of_pos heps
  have hL5 : Real.log z ≤ (Real.log z)^5 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL : 1 ≤ (Real.log z)^4) hL0.le
    nlinarith
  have hpay : 8*C ≤ (Real.log z)^5*(eta*eps^2) := by
    have hh := (div_le_iff₀ (mul_pos heta he2)).mp ((le_max_right _ _).trans hzL)
    exact hh.trans (mul_le_mul_of_nonneg_right hL5 (mul_pos heta he2).le)
  have hfirst : 4*C/(eta*(Real.log z)^5) ≤ eps^2/2 := by
    apply (div_le_iff₀ (by positivity : 0 < eta*(Real.log z)^5)).mpr
    nlinarith
  have hpower : 0 < z^((92 : ℝ)/100) := Real.rpow_pos_of_pos hz0 _
  have hsecond : 1/z^((92 : ℝ)/100) ≤ eps^2/2 := by
    apply (div_le_iff₀ hpower).mpr
    have hh := (div_le_iff₀ he2).mp hzpow
    nlinarith
  refine ⟨hz,hL,?_⟩
  intro R N n hR hRz hN hcount
  apply (collision_error_bound z R N n eta C hz hR hRz hN heta hC hL hcount).trans
  linarith

end ErdosSourceCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_NormalizedCollisionSmallness
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision

theorem normalized_collision_bound (I K C n R N L : ℝ)
    (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hn : 0 < n) (hN : 0 < N) (hL : 0 < L)
    (hcollision : I^2 ≤ K*(C*N^2+I)) (hthin : K ≤ n*R/L^6) (hI : I ≤ n*N) :
    (I/(n*N))^2 ≤ C*R/(n*L^6)+R/(N*L^6) := by
  have hup : I^2 ≤ (n*R/L^6)*(C*N^2+n*N) := by
    calc
      _ ≤ K*(C*N^2+I) := hcollision
      _ ≤ K*(C*N^2+n*N) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hI) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hthin (by positivity)
  rw [div_pow]
  calc
    _ ≤ ((n*R/L^6)*(C*N^2+n*N))/(n*N)^2 :=
      div_le_div_of_nonneg_right hup (sq_nonneg _)
    _ = _ := by field_simp

end ErdosLineCollision

end

section

open Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosLineCollision

theorem uniform_normalized_collision (C eta eps : ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ inc K R N n : ℝ,
      1 < R → R ≤ z^((1 : ℝ)/100) → z^((93 : ℝ)/100) ≤ N →
      eta*R/(4*Real.log R) ≤ n → 0 ≤ K →
      inc^2 ≤ K*(C*N^2+inc) → K ≤ n*R/(Real.log z)^6 → inc ≤ n*N →
      inc ≤ eps*n*N := by
  filter_upwards [uniform_collision_error C eta eps hC heta heps] with z hz
  refine ⟨hz.1,?_⟩
  intro inc K R N n hR hRz hN hcount hK hcoll hthin hI
  have hz0 : 0 < z := by linarith [hz.1]
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hn : 0 < n := (div_pos (mul_pos heta hR0) (mul_pos (by norm_num) hlogR)).trans_le hcount
  have hNp : 0 < N := (Real.rpow_pos_of_pos hz0 _).trans_le hN
  have hL : 0 < Real.log z := by linarith [hz.2.1]
  have hsq := (normalized_collision_bound inc K C n R N (Real.log z) hK hC hn hNp hL hcoll hthin hI).trans
    (hz.2.2 R N n hR hRz hN hcount)
  have hratio : inc/(n*N) ≤ eps := by nlinarith [sq_nonneg (inc/(n*N)-eps)]
  have hh := (div_le_iff₀ (mul_pos hn hNp)).mp hratio
  nlinarith

end ErdosSourceCollision

end

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

end ErdosInverseIncidence

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

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem exists_intercept_reduction (l : PrimitiveIntegerLine) : Nonempty (InterceptReduction l) := by
  let g : ℕ := Int.gcd l.intercept (l.denominator : ℤ)
  have hd : (0 : ℤ) < l.denominator := by exact_mod_cast l.denominator_pos
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_right _ (ne_of_gt hd)
  obtain ⟨A,D,hcop,hA,hD⟩ := Int.exists_gcd_one hg
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hDpos : 0 < D := by nlinarith
  have hDt : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hDpos.le
  have hDn : 0 < D.toNat := by omega
  have hred : Nat.Coprime A.natAbs D.toNat := by
    have hh : Int.gcd A (D.toNat : ℤ) = 1 := by rwa [hDt]
    simpa only [Int.gcd_def,Int.natAbs_natCast,Nat.Coprime] using hh
  let r : ℚ := Rat.mk' A D.toNat hDn.ne' hred
  have hden : l.denominator = g*r.den := by
    change l.denominator = g*D.toNat
    have hh : (l.denominator : ℤ) = (g : ℤ)*(D.toNat : ℤ) := by rw [hDt];nlinarith [hD]
    exact_mod_cast hh
  have hint : l.intercept = (g : ℤ)*r.num := by
    change l.intercept = (g : ℤ)*A
    nlinarith [hA]
  exact ⟨⟨r,g,hg,hden,hint⟩⟩

end ErdosPrimitiveIntercept

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem InterceptReduction.factor_dvd_denominator {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.factor ∣ l.denominator := ⟨r.rational.den,r.denominator_eq⟩

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BadPrimeProduct
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine ErdosInverseAlignment

theorem InterceptReduction.prime_alignment {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℤ × ℤ) (hp : l.Contains p) (ell : ℕ) (hell : Nat.Prime ell)
    (hx : (ell : ℤ) ∣ p.1) (hclass : (p.2 : ZMod ell) = (a ell : ZMod ell))
    (hfactor : ¬ell ∣ r.factor) : aligns a r.rational ell := by
  let : Fact (Nat.Prime ell) := ⟨hell⟩
  have hg : (r.factor : ZMod ell) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr hfactor
  have hx0 : (p.1 : ZMod ell) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  unfold PrimitiveIntegerLine.Contains at hp
  rw [r.denominator_eq,r.intercept_eq] at hp
  have hh := congrArg (fun n : ℤ => (n : ZMod ell)) hp
  have he : (r.factor : ZMod ell)*((r.rational.den : ZMod ell)*(a ell : ZMod ell)) =
      (r.factor : ZMod ell)*(r.rational.num : ZMod ell) := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast,Nat.cast_mul,hx0,
      mul_zero,zero_add,hclass,mul_assoc] using hh
  exact mul_left_cancel₀ hg he

theorem InterceptReduction.nonaligned_prime_dvd_factor {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (p : ℤ × ℤ) (hp : l.Contains p)
    (ell : ℕ) (hell : Nat.Prime ell) (hx : (ell : ℤ) ∣ p.1)
    (hclass : (p.2 : ZMod ell) = (a ell : ZMod ell)) (hna : ¬aligns a r.rational ell) :
    ell ∣ r.factor := by
  by_contra hh
  exact hna (r.prime_alignment a p hp ell hell hx hclass hh)

end ErdosPrimitiveIntercept

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine ErdosInverseAlignment

theorem InterceptReduction.bad_product_dvd_factor {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (q : ℕ) (b : ℤ)
    (hp : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors, (b : ZMod ell) = (a ell : ZMod ell)) :
    badPrimeProduct a r.rational q ∣ r.factor := by
  classical
  apply Finset.prod_primes_dvd r.factor
  · intro ell hell
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hell).1).prime
  · intro ell hell
    obtain ⟨hfactor,hna⟩ := Finset.mem_filter.mp hell
    have he := Nat.mem_primeFactors.mp hfactor
    exact r.nonaligned_prime_dvd_factor a ((q : ℤ),b) hp ell he.1
      (by change (ell : ℤ) ∣ (q : ℤ);exact_mod_cast he.2.1) (hclass ell hfactor) hna

theorem InterceptReduction.structure_bound {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (q : ℕ) (b : ℤ)
    (hp : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors, (b : ZMod ell) = (a ell : ZMod ell)) :
    r.rational.den*badPrimeProduct a r.rational q ≤ l.denominator := by
  have hle := Nat.le_of_dvd r.factor_pos (r.bad_product_dvd_factor a q b hp hclass)
  calc
    _ ≤ r.rational.den*r.factor := Nat.mul_le_mul_left _ hle
    _ = l.denominator := by rw [r.denominator_eq,mul_comm]

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PreciseIncidenceMoment
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision
open ErdosInverseIncidence
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem precise_multiplicity_square_upper {α β : Type*} (A : Finset α) (Q : Finset β)
    (R : α → β → Prop) (K : ℝ) (hK : 0 ≤ K)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((Q.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ Q,(multiplicity A R p)^2) ≤
      (∑ p ∈ Q,multiplicity A R p)+K*(A.card : ℝ)^2 := by
  rw [multiplicity_square_sum,multiplicity_sum]
  calc
    _ ≤ ∑ a ∈ A,∑ b ∈ A,((if b=a then (degree Q R a : ℝ) else 0)+K) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : b=a
      · subst b
        simp only [and_self,degree]
        exact le_add_of_nonneg_right hK
      · rw [ite_eq_right hab,zero_add]
        exact hpair a ha b hb (Ne.symm hab)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const,nsmul_eq_mul]
      have he : (∑ a ∈ A,if a ∈ A then (degree Q R a : ℝ) else 0) =
          ∑ a ∈ A,(degree Q R a : ℝ) := by simp
      rw [he]
      ring

theorem precise_incidence_cauchy {α β : Type*} (A : Finset α) (Q : Finset β)
    (R : α → β → Prop) (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hQ : (Q.card : ℝ) ≤ B)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((Q.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ Q,multiplicity A R p)^2 ≤
      B*(K*(A.card : ℝ)^2+∑ p ∈ Q,multiplicity A R p) := by
  have hcs : (∑ p ∈ Q,multiplicity A R p)^2 ≤ (Q.card : ℝ)*(∑ p ∈ Q,(multiplicity A R p)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Q (fun _ => (1 : ℝ)) (multiplicity A R)
  have hup := precise_multiplicity_square_upper A Q R K hK hpair
  calc
    _ ≤ (Q.card : ℝ)*(∑ p ∈ Q,(multiplicity A R p)^2) := hcs
    _ ≤ B*(∑ p ∈ Q,(multiplicity A R p)^2) := mul_le_mul_of_nonneg_right hQ
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ B*((∑ p ∈ Q,multiplicity A R p)+K*(A.card : ℝ)^2) := mul_le_mul_of_nonneg_left hup hB
    _ = _ := by ring

end ErdosLineCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LargePrimeDivisors
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision

theorem dividingPrimes_card_bound (P : Finset ℕ) (m : ℤ) (hm : m ≠ 0)
    (hprime : ∀ p ∈ P, Nat.Prime p) (z alpha C : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P, z^alpha ≤ (p : ℝ)) (hheight : |(m : ℝ)| ≤ z^C) :
    ((dividingPrimes P m).card : ℝ) ≤ C/alpha := by
  classical
  have hd : (∏ p ∈ dividingPrimes P m,p) ∣ m.natAbs :=
    Finset.prod_primes_dvd m.natAbs
      (fun p hp => (hprime p (Finset.mem_filter.mp hp).1).prime)
      (fun _ hp => Int.natCast_dvd.mp (Finset.mem_filter.mp hp).2)
  have hprod := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hd
  have hpow : z^(alpha*((dividingPrimes P m).card : ℝ)) ≤ z^C := by
    calc
      _ = ∏ _p ∈ dividingPrimes P m,z^alpha := by
        rw [Finset.prod_const,Real.rpow_mul_natCast (by linarith : 0 ≤ z)]
      _ ≤ ∏ p ∈ dividingPrimes P m,(p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (by linarith) _)
          (fun p hp => hlarge p (Finset.mem_filter.mp hp).1)
      _ = ((∏ p ∈ dividingPrimes P m,p : ℕ) : ℝ) := by simp
      _ ≤ (m.natAbs : ℝ) := by exact_mod_cast hprod
      _ = |(m : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
      _ ≤ _ := hheight
  have hh := (Real.rpow_le_rpow_left_iff hz).mp hpow
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem integer_difference_abs_le {x y : ℤ} {S : ℝ}
    (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) :
    |((x-y : ℤ) : ℝ)| ≤ S := by
  rw [Int.cast_sub,abs_le]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

end ErdosLineCollision

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

end ErdosInverseAlignment



namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem InterceptReduction.denominator_le {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.rational.den ≤ l.denominator := by
  rw [r.denominator_eq]
  simpa using Nat.mul_le_mul_right r.rational.den (Nat.succ_le_of_lt r.factor_pos)

theorem InterceptReduction.numerator_abs_le {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.rational.num.natAbs ≤ l.intercept.natAbs := by
  rw [r.intercept_eq,Int.natAbs_mul,Int.natAbs_natCast]
  simpa using Nat.mul_le_mul_right r.rational.num.natAbs (Nat.succ_le_of_lt r.factor_pos)

theorem InterceptReduction.height_transfer {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (Hden Hnum : ℝ) (hd : (l.denominator : ℝ) ≤ Hden) (hn : |(l.intercept : ℝ)| ≤ Hnum) :
    (r.rational.den : ℝ) ≤ Hden ∧ |(r.rational.num : ℝ)| ≤ Hnum := by
  have hden : (r.rational.den : ℝ) ≤ l.denominator := by exact_mod_cast r.denominator_le
  have hnum : |(r.rational.num : ℝ)| ≤ |(l.intercept : ℝ)| := by
    have hh : (r.rational.num.natAbs : ℝ) ≤ l.intercept.natAbs := by exact_mod_cast r.numerator_abs_le
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  exact ⟨hden.trans hd,hnum.trans hn⟩

end ErdosPrimitiveIntercept



namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine

theorem structured_of_line_alignment {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) (b : ℤ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp)
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hline : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors,(b : ZMod ell) = (a ell : ZMod ell))
    (halign : aligns a r.rational p) : Structured P a S R Z cp p q := by
  refine ⟨r.rational,hlist,halign,?_⟩
  have hh : ((r.rational.den*badPrimeProduct a r.rational q : ℕ) : ℝ) ≤ l.denominator :=
    Nat.cast_le.mpr (r.structure_bound a q b hline hclass)
  exact hh.trans hden

end ErdosInverseStructured



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

theorem unaligned_numerator_ne_zero {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℕ) (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator)
    (hna : ¬aligns a r.rational p) :
    (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) ≠ 0 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hpg : ¬p ∣ r.factor := fun h => hpd (h.trans r.factor_dvd_denominator)
  have hg : (r.factor : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr hpg
  have hdiff : (r.rational.den : ZMod p)*(a p : ZMod p)-(r.rational.num : ZMod p) ≠ 0 :=
    sub_ne_zero.mpr hna
  have he : (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) =
      (r.factor : ZMod p)*((r.rational.den : ZMod p)*(a p : ZMod p)-(r.rational.num : ZMod p)) := by
    rw [r.denominator_eq,r.intercept_eq,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    ring
  rw [he]
  exact mul_ne_zero hg hdiff

theorem point_residue_eq_slopeClass {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℕ) (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator)
    (hna : ¬aligns a r.rational p) (v : ℤ × ℤ) (hv : l.Contains v) (s : ℤ)
    (hinc : (v.2 : ZMod p) = (a p : ZMod p)-(s : ZMod p)*(v.1 : ZMod p)) :
    (v.1 : ZMod p) = slopeClass l (a p) p hp s := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hnum := unaligned_numerator_ne_zero r a p hp hpd hna
  have hvZ : (l.denominator : ZMod p)*(v.2 : ZMod p) =
      (l.slope : ZMod p)*(v.1 : ZMod p)+(l.intercept : ZMod p) := by
    have h := congrArg (fun n : ℤ => (n : ZMod p)) hv
    simpa only [PrimitiveIntegerLine.Contains,Int.cast_mul,Int.cast_add,Int.cast_natCast] using h
  have he : ((l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p))*(v.1 : ZMod p) =
      (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) := by
    linear_combination (l.denominator : ZMod p)*hinc-hvZ
  have hcoeff : (l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p) ≠ 0 := by
    intro hz
    exact hnum (by simpa only [hz,zero_mul] using he.symm)
  unfold slopeClass
  apply (eq_div_iff hcoeff).mpr
  simpa only [mul_comm] using he

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

theorem occupiedClasses_subset_slope_image {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (X : Finset (ℤ × ℤ)) (hline : ∀ v ∈ X, l.Contains v) (a : ℕ → ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator) (hna : ¬aligns a r.rational p) (T : Finset ℤ) :
    occupiedClasses X (a p) p T ⊆ T.image (slopeClass l (a p) p hp) := by
  classical
  intro t ht
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hvX,s,hs,hinc⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨s,hs,(point_residue_eq_slopeClass r a p hp hpd hna v
    (hline v hvX) s hinc).symm⟩

theorem occupiedClasses_card_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (X : Finset (ℤ × ℤ)) (hline : ∀ v ∈ X, l.Contains v) (a : ℕ → ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator) (hna : ¬aligns a r.rational p) (T : Finset ℤ) :
    (occupiedClasses X (a p) p T).card ≤ T.card := by
  classical
  exact (Finset.card_le_card (occupiedClasses_subset_slope_image r X hline a p hp hpd hna T)).trans
    (Finset.card_image_le)

end ErdosLineCollision



namespace ErdosLineCollision
attribute [local instance] Classical.propDecidable

theorem row_modulus_mem {P : Finset ℕ} {X : Finset (ℤ × ℤ)} {a : ℕ → ℤ} {T : ℕ → Finset ℤ}
    {row : ℕ × ℕ} (hr : row ∈ occupiedRows P X a T) : row.1 ∈ P := by
  classical
  obtain ⟨p,hp,hpRow⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨c,hc,hrow⟩ := Finset.mem_image.mp hpRow
  subst row
  exact hp

theorem point_rows_eq (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) :
    (occupiedRows P X a T).filter (RowIncidence X a T v) =
      (P.filter (fun p => v ∈ incidentPoints X (a p) p (T p))).image
        (fun p => (p,(v.1 : ZMod p).val)) := by
  classical
  ext row
  constructor
  · intro hr
    obtain ⟨hrow,hinc,hval⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_image.mpr ⟨row.1,Finset.mem_filter.mpr ⟨row_modulus_mem hrow,hinc⟩,
      Prod.ext rfl hval⟩
  · intro hr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hpP,hv⟩ := Finset.mem_filter.mp hp
    have hclass : (v.1 : ZMod p) ∈ occupiedClasses X (a p) p (T p) :=
      Finset.mem_image.mpr ⟨v,hv,rfl⟩
    refine Finset.mem_filter.mpr ⟨?_,hv,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨(v.1 : ZMod p),hclass,rfl⟩⟩

theorem point_rows_card (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) :
    ((occupiedRows P X a T).filter (RowIncidence X a T v)).card =
      (P.filter (fun p => v ∈ incidentPoints X (a p) p (T p))).card := by
  classical
  rw [point_rows_eq]
  apply Finset.card_image_of_injective
  intro p q he
  exact congrArg Prod.fst he

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem occupiedRows_card_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hline : ∀ v ∈ X, l.Contains v) (hP : ∀ p ∈ P, Nat.Prime p)
    (hpd : ∀ p ∈ P, ¬p ∣ l.denominator) (hna : ∀ p ∈ P, ¬aligns a r.rational p) :
    (occupiedRows P X a T).card ≤ ∑ p ∈ P,(T p).card := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro p hp
  exact Finset.card_image_le.trans (occupiedClasses_card_le r X hline a p (hP p hp) (hpd p hp) (hna p hp) (T p))

theorem commonRows_modulus_injective (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v w : ℤ × ℤ) :
    Set.InjOn Prod.fst (commonRows P X a T v w : Set (ℕ × ℕ)) := by
  intro row hr row' hr' he
  have hval := ((Finset.mem_filter.mp hr).2).1.2
  have hval' := ((Finset.mem_filter.mp hr').2).1.2
  rw [he] at hval
  exact Prod.ext he (hval.symm.trans hval')

theorem commonRows_modulus_divides (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (hP : ∀ p ∈ P, Nat.Prime p) (v w : ℤ × ℤ)
    (row : ℕ × ℕ) (hr : row ∈ commonRows P X a T v w) : (row.1 : ℤ) ∣ v.1-w.1 := by
  have hp := row_modulus_mem (Finset.mem_filter.mp hr).1
  let : Fact (Nat.Prime row.1) := ⟨hP row.1 hp⟩
  have hval := ((Finset.mem_filter.mp hr).2).1.2
  have hval' := ((Finset.mem_filter.mp hr).2).2.2
  have he : (v.1 : ZMod row.1) = (w.1 : ZMod row.1) :=
    ZMod.val_injective row.1 (hval.trans hval'.symm)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub,he,sub_self]

theorem commonRows_card_le (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hP : ∀ p ∈ P, Nat.Prime p) (v w : ℤ × ℤ) (hx : v.1 ≠ w.1)
    (z alpha C : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hheight : |((v.1-w.1 : ℤ) : ℝ)| ≤ z^C) :
    ((commonRows P X a T v w).card : ℝ) ≤ C/alpha := by
  classical
  have hsub : (commonRows P X a T v w).image Prod.fst ⊆ dividingPrimes P (v.1-w.1) := by
    intro p hp
    obtain ⟨row,hrow,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨row_modulus_mem (Finset.mem_filter.mp hrow).1,
      commonRows_modulus_divides P X a T hP v w row hrow⟩
  have hc : (commonRows P X a T v w).card ≤ (dividingPrimes P (v.1-w.1)).card := by
    rw [← Finset.card_image_of_injOn (commonRows_modulus_injective P X a T v w)]
    exact Finset.card_le_card hsub
  apply (show ((commonRows P X a T v w).card : ℝ) ≤ (dividingPrimes P (v.1-w.1)).card by exact_mod_cast hc).trans
  exact dividingPrimes_card_bound P (v.1-w.1) (sub_ne_zero.mpr hx) hP z alpha C hz ha hlarge hheight

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosInverseIncidence
attribute [local instance] Classical.propDecidable

theorem row_multiplicity_sum (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) :
    (∑ row ∈ occupiedRows P X a T,multiplicity X (RowIncidence X a T) row) =
      ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ) := by
  classical
  let R : (ℤ × ℤ) → ℕ → Prop := fun v p => v ∈ incidentPoints X (a p) p (T p)
  have hdegree (v : ℤ × ℤ) : degree (occupiedRows P X a T) (RowIncidence X a T) v = degree P R v :=
    by simpa only [ErdosInverseIncidence.degree,R] using point_rows_card P X a T v
  have hcount (p : ℕ) : multiplicity X R p = ((incidentPoints X (a p) p (T p)).card : ℝ) := by
    have he : X.filter (fun v => v ∈ incidentPoints X (a p) p (T p)) = incidentPoints X (a p) p (T p) := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    have hh : (∑ v ∈ X,if v ∈ incidentPoints X (a p) p (T p) then (1 : ℝ) else 0) =
        ((X.filter (fun v => v ∈ incidentPoints X (a p) p (T p))).card : ℝ) :=
      Finset.sum_boole (fun v => v ∈ incidentPoints X (a p) p (T p)) X
    rw [he] at hh
    have hsum : multiplicity X R p =
        ∑ v ∈ X,if v ∈ incidentPoints X (a p) p (T p) then (1 : ℝ) else 0 := by
      unfold ErdosInverseIncidence.multiplicity
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hmem : v ∈ incidentPoints X (a p) p (T p) <;>
        simp [ErdosInverseIncidence.bit,R,hmem]
    exact hsum.trans hh
  calc
    _ = ∑ v ∈ X,(degree (occupiedRows P X a T) (RowIncidence X a T) v : ℝ) := multiplicity_sum _ _ _
    _ = ∑ v ∈ X,(degree P R v : ℝ) := by simp_rw [hdegree]
    _ = ∑ p ∈ P,multiplicity X R p := (multiplicity_sum X P R).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => hcount p)

theorem total_incidence_le_product (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) :
    (∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤ (P.card : ℝ)*(X.card : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ P,(X.card : ℝ) := Finset.sum_le_sum (fun p _ => by
      have hc : (incidentPoints X (a p) p (T p)).card ≤ X.card := Finset.card_filter_le X _
      exact Nat.cast_le.mpr hc)
    _ = _ := by simp

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosInverseIncidence ErdosConvexGraph

theorem actual_collision_bound {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hline : ∀ v ∈ X,l.Contains v) (hP : ∀ p ∈ P,Nat.Prime p)
    (hpd : ∀ p ∈ P,¬p ∣ l.denominator) (hna : ∀ p ∈ P,¬aligns a r.rational p)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (S z alpha : ℝ)
    (hbox : ∀ v ∈ X,InSquare S v) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hS : S ≤ z^3) :
    (∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ))^2 ≤
      (∑ p ∈ P,((T p).card : ℝ))*
        ((3/alpha)*(X.card : ℝ)^2+∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ)) := by
  classical
  have hK : (0 : ℝ) ≤ 3/alpha := by positivity
  have hB : 0 ≤ ∑ p ∈ P,((T p).card : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hQ : ((occupiedRows P X a T).card : ℝ) ≤ ∑ p ∈ P,((T p).card : ℝ) := by
    exact_mod_cast occupiedRows_card_le r P X a T hline hP hpd hna
  have hpair : ∀ v ∈ X,∀ w ∈ X,v ≠ w →
      (((occupiedRows P X a T).filter
        (fun row => RowIncidence X a T v row ∧ RowIncidence X a T w row)).card : ℝ) ≤ 3/alpha := by
    intro v hv w hw hne
    have hx : v.1 ≠ w.1 := fun he => hne (hinj hv hw he)
    have hh : |((v.1-w.1 : ℤ) : ℝ)| ≤ z^(3 : ℝ) := by
      have he : z^(3 : ℝ) = z^3 := Real.rpow_natCast z 3
      rw [he]
      exact (integer_difference_abs_le (hbox v hv).1 (hbox w hw).1).trans hS
    exact commonRows_card_le P X a T hP v w hx z alpha 3 hz ha hlarge hh
  have hh := precise_incidence_cauchy X (occupiedRows P X a T) (RowIncidence X a T)
    (3/alpha) (∑ p ∈ P,((T p).card : ℝ)) hK hB hQ hpair
  rwa [row_multiplicity_sum] at hh

end ErdosLineCollision


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeHitRepresentative
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem primeHitRepresentative_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ primeHitRepresentative q hq a ∧ primeHitRepresentative q hq a ≤ q ∧
      ∀ n : ℕ,(∀ p ∈ q.primeFactors,n%p = a p%p) ↔ Nat.ModEq q n (primeHitRepresentative q hq a) :=
  (exists_prime_hit_representative q hq a).choose_spec

end ErdosInverseHits

end

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

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_W_power_quarter (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < sourceW z ∧ (sourceW z)^C ≤ z^((1 : ℝ)/4) := by
  have hs := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1/4)).bound zero_lt_one
  have hLL := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [source_B_bounds,hs,hLL,eventually_gt_atTop (1 : ℝ)] with z hB hz hlog hz1
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < Real.log z := Real.log_pos hz1
  have hLL1 : 1 ≤ Real.log (Real.log z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlog
    simpa only [Real.log_exp] using h
  have hsquare : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hWL : sourceW z ≤ Real.log z := div_le_self hL0.le hsquare
  have hW1 : 1 < sourceW z := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hB.1
  refine ⟨hW1,?_⟩
  have hh : (Real.log z)^C ≤ z^((1 : ℝ)/4) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0.le C),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/4)),one_mul] using hz
  exact (Real.rpow_le_rpow (by linarith) hWL hC).trans hh

theorem source_Y_three_halves :
    ∀ᶠ z : ℝ in atTop, z^((3 : ℝ)/2) ≤ (sourceY z : ℝ) := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hs,eventually_ge_atTop (2 : ℝ)] with z hz hz2
  have hz0 : 0 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hL2 : 0 < (Real.log z)^2 := sq_pos_of_pos hL
  have hh : (Real.log z)^2 ≤ (1/2 : ℝ)*z^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log z)),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/2))] using hz
  have hp : z^((1 : ℝ)/2)*z^((3 : ℝ)/2) = z^2 := by
    rw [← Real.rpow_add hz0]
    norm_num
  have hmul : 2*z^((3 : ℝ)/2)*(Real.log z)^2 ≤ z^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz0.le ((3 : ℝ)/2))]
  have hquot : 2*z^((3 : ℝ)/2) ≤ z^2/(Real.log z)^2 := (le_div_iff₀ hL2).mpr hmul
  have hfloor := Nat.lt_floor_add_one (z^2/(Real.log z)^2)
  have hone : 1 ≤ z^((3 : ℝ)/2) := Real.one_le_rpow (by linarith) (by norm_num)
  change z^((3 : ℝ)/2) ≤ (⌊z^2/(Real.log z)^2⌋₊ : ℝ)
  linarith

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_parent_square_lower (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C → z ≤ S := by
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 24/100)).eventually_ge_atTop 2
  filter_upwards [source_W_power_quarter C hC,source_Y_three_halves,hquarter,
    eventually_gt_atTop (1 : ℝ)] with z hW hY htwo hz
  have hz0 : 0 < z := by linarith
  refine ⟨hz,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hY0 : (0 : ℝ) < sourceY z := (Real.rpow_pos_of_pos hz0 _).trans_le hY
  have hP : p ≤ z^((1 : ℝ)/4) := by
    calc
      p ≤ 2*R := hpR
      _ ≤ 2*z^((1 : ℝ)/100) := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ z^((24 : ℝ)/100)*z^((1 : ℝ)/100) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz0.le _)
      _ = z^((1 : ℝ)/4) := by rw [← Real.rpow_add hz0];norm_num
  have hratio := (Real.logb_le_iff_le_rpow hW.1 (div_pos hY0 (mul_pos hp hq))).mp hlen
  have hmul : (sourceY z : ℝ) ≤ (sourceW z)^C*(p*q) := (div_le_iff₀ (mul_pos hp hq)).mp hratio
  have hsmall : (sourceW z)^C*p ≤ z^((1 : ℝ)/2) := by
    calc
      _ ≤ z^((1 : ℝ)/4)*z^((1 : ℝ)/4) := mul_le_mul hW.2 hP hp.le
        (Real.rpow_nonneg hz0.le _)
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  have hle : z^((3 : ℝ)/2) ≤ z^((1 : ℝ)/2)*q := by
    apply hY.trans
    apply hmul.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hq.le
  have he : z^((3 : ℝ)/2) = z^((1 : ℝ)/2)*z := by
    have hh := Real.rpow_add hz0 ((1 : ℝ)/2) 1
    norm_num at hh
    exact hh
  rw [he] at hle
  exact (le_of_mul_le_mul_left hle (Real.rpow_pos_of_pos hz0 ((1 : ℝ)/2))).trans hqS

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_Z_ge_two : ∀ᶠ z : ℝ in atTop, 2 ≤ sourceZ z := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with z hz
  have hL : 0 < Real.log z := (Real.exp_pos 1).trans_le hz
  have hLL : 1 ≤ Real.log (Real.log z) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hz
    simpa only [Real.log_exp] using hh
  have hLLL : Real.log (Real.log z) ≤ Real.log z := by
    have hh := Real.log_le_sub_one_of_pos hL
    linarith
  have hratio : 1 ≤ Real.log z/Real.log (Real.log z) :=
    (one_le_div (by linarith)).mpr hLLL
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh ⊢
    exact hh
  exact hexp.trans (Real.exp_le_exp.mpr hratio)

theorem extraction_small_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S)
    (hbig : 728 < z^((19 : ℝ)/75)) :
    728*R^4*Z^4 < S^((1 : ℝ)/3) := by
  have hz0 : 0 < z := by linarith
  have hR4 : R^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hZ4 : Z^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  calc
    _ ≤ 728*z^((4 : ℝ)/100)*z^((4 : ℝ)/100) := by gcongr
    _ = 728*z^((2 : ℝ)/25) := by rw [mul_assoc,← Real.rpow_add hz0];norm_num
    _ < z^((19 : ℝ)/75)*z^((2 : ℝ)/25) :=
      mul_lt_mul_of_pos_right hbig (Real.rpow_pos_of_pos hz0 _)
    _ = z^((1 : ℝ)/3) := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S^((1 : ℝ)/3) := Real.rpow_le_rpow hz0.le hSz (by norm_num)

theorem minimum_line_size_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 < R) (hZ : 0 < Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S) :
    z^((93 : ℝ)/100) ≤ S/(R*Z^6) := by
  have hz0 : 0 < z := by linarith
  have hZ6 : Z^6 ≤ z^((6 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^6 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hprod : R*Z^6 ≤ z^((7 : ℝ)/100) := by
    calc
      _ ≤ z^((1 : ℝ)/100)*z^((6 : ℝ)/100) := by gcongr
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  apply (le_div_iff₀ (mul_pos hR (pow_pos hZ 6))).mpr
  calc
    _ ≤ z^((93 : ℝ)/100)*z^((7 : ℝ)/100) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hz0.le _)
    _ = z := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S := hSz

end ErdosSourceLineBudget

end

section

namespace ErdosSourceLineBudget

theorem finite_extraction_budget (D : ℕ) (R S Z : ℝ) (hD : (D : ℝ) ≤ R)
    (hR : 0 < R) (hS : 1 ≤ S) (hZ : 2 ≤ Z)
    (hsmall : 728*R^4*Z^4 < S^((1 : ℝ)/3)) :
    182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*(S/(R*Z^6)) < S/Z^4 := by
  have hS0 : 0 < S := by linarith
  have hZ0 : 0 < Z := by linarith
  have hu : 1 ≤ S^((2 : ℝ)/3) := Real.one_le_rpow hS (by norm_num)
  have hprod : S^((1 : ℝ)/3)*S^((2 : ℝ)/3) = S := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hlarge : 728*R^4*Z^4*S^((2 : ℝ)/3) < S := by
    have hh := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hS0 ((2 : ℝ)/3))
    rwa [hprod] at hh
  have hnonlinear : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) < S/(2*Z^4) := by
    have hpower : (D : ℝ)^4 ≤ R^4 := by gcongr
    have hfirst : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) ≤ 364*R^4*S^((2 : ℝ)/3) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpower) (show 0 ≤ 1+S^((2 : ℝ)/3) by positivity),
        mul_nonneg (pow_nonneg hR.le 4) (sub_nonneg.mpr hu)]
    apply hfirst.trans_lt
    apply (lt_div_iff₀ (by positivity : 0 < 2*Z^4)).mpr
    nlinarith
  have hlinear : (D : ℝ)*(S/(R*Z^6)) ≤ S/(2*Z^4) := by
    calc
      _ ≤ R*(S/(R*Z^6)) := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = S/Z^6 := by field_simp
      _ ≤ S/(2*Z^4) := by
        apply div_le_div_of_nonneg_left hS0.le (by positivity)
        have hs : 2 ≤ Z^2 := by nlinarith
        nlinarith [mul_nonneg (pow_nonneg hZ0.le 4) (sub_nonneg.mpr hs)]
  calc
    _ < S/(2*Z^4)+S/(2*Z^4) := add_lt_add_of_lt_of_le hnonlinear hlinear
    _ = _ := by ring

end ErdosSourceLineBudget

end

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

theorem sourceDegree_le {z R : ℝ} (hR : 0 ≤ R) :
    (sourceDegree z R : ℝ) ≤ R/(Real.log z)^2 :=
  Nat.floor_le (div_nonneg hR (sq_nonneg _))

theorem sourceDegree_le_R {z R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ Real.log z) :
    (sourceDegree z R : ℝ) ≤ R :=
  (sourceDegree_le hR).trans (div_le_self hR (by nlinarith))

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial

theorem uniform_extraction_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C →
      z^((93 : ℝ)/100) ≤ S/(R*(sourceZ z)^6) ∧ 1 ≤ S/(R*(sourceZ z)^6) ∧
      182*(sourceDegree z R : ℝ)^4*(1+S^((2 : ℝ)/3))+
        (sourceDegree z R : ℝ)*(S/(R*(sourceZ z)^6)) < S/(sourceZ z)^4 := by
  have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 19/75)).eventually_gt_atTop 728
  filter_upwards [source_parent_square_lower C hC,sourceZ_le_small_power,source_Z_ge_two,hbig,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with z hparent hZ hZ2 hlarge hL
  refine ⟨hparent.1,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hSz := hparent.2 p q R S hp hq hpR hR hqS hlen
  have hR0 : 0 < R := by linarith
  have hS1 : 1 ≤ S := hparent.1.le.trans hSz
  have hmin := minimum_line_size_power hparent.1 hR0 hZ.2.1 hR hZ.2.2 hSz
  have hmin1 : 1 ≤ S/(R*(sourceZ z)^6) :=
    (Real.one_le_rpow hparent.1.le (by norm_num : (0 : ℝ) ≤ 93/100)).trans hmin
  have hsmall := extraction_small_power hparent.1 hR0.le hZ.2.1.le hR hZ.2.2 hSz hlarge
  exact ⟨hmin,hmin1,finite_extraction_budget (sourceDegree z R) R S (sourceZ z)
    (sourceDegree_le_R hR0.le hL) hR0 hS1 hZ2 hsmall⟩

end ErdosSourceLineBudget

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RealCoprimeResidueCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem mem_crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (r : ZMod (∏ i,m i)) :
    r ∈ crtResidues m hcop E ↔ ∀ i,(ZMod.prodEquivPi m hcop r) i ∈ E i := by
  constructor
  · intro hr
    obtain ⟨f,hf,hfr⟩ := Finset.mem_map.mp hr
    have he : ZMod.prodEquivPi m hcop r = f := by
      rw [← hfr]
      exact (ZMod.prodEquivPi m hcop).apply_symm_apply f
    rw [he]
    exact Fintype.mem_piFinset.mp hf
  · intro hr
    exact Finset.mem_map.mpr ⟨ZMod.prodEquivPi m hcop r,Fintype.mem_piFinset.mpr hr,
      (ZMod.prodEquivPi m hcop).symm_apply_apply r⟩

theorem crtResidues_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (E : ∀ i,Finset (ZMod (m i))) :
    (crtResidues m hcop E).card = ∏ i,(E i).card := by
  rw [crtResidues,Finset.card_map,Fintype.card_piFinset]

theorem intCast_mem_crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (s : ℤ) :
    (s : ZMod (∏ i,m i)) ∈ crtResidues m hcop E ↔ ∀ i,(s : ZMod (m i)) ∈ E i := by
  rw [mem_crtResidues]
  have he (i : ι) : ZMod.prodEquivPi m hcop (s : ZMod (∏ j,m j)) i = (s : ZMod (m i)) := by
    rw [ZMod.prodEquivPi_apply]
    exact map_intCast (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) s
  simp only [he]

end ErdosInverseCRT



namespace Erdos66Dependency.SingleResidueCount

open Finset

theorem count_exact (a b Q r : ℤ) (hQ : 0 < Q) :
    ((residueClass a b Q r).card : ℤ) =
      max (⌈((b : ℚ) - r) / Q⌉ - ⌈((a : ℚ) - r) / Q⌉) 0 :=
  Int.Ico_filter_modEq_card a b hQ r

lemma count_error_rat (a b Q r : ℤ) (hQ : 0 < Q) (hab : a ≤ b) :
    |((residueClass a b Q r).card : ℚ) - ((b : ℚ) - a) / Q| ≤ 1 := by
  have hQQ : (0:ℚ) < Q := by exact_mod_cast hQ
  have hx : ((a : ℚ) - r) / Q ≤ ((b : ℚ) - r) / Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast sub_le_sub_right hab r) hQQ.le
  have hceil := Int.ceil_mono hx
  have hcount := count_exact a b Q r hQ
  rw [max_eq_left (sub_nonneg.mpr hceil)] at hcount
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) hcount
  push_cast at hcast
  rw [hcast]
  have ha := Int.le_ceil (((a : ℚ) - r) / Q)
  have ha' := Int.ceil_lt_add_one (((a : ℚ) - r) / Q)
  have hb := Int.le_ceil (((b : ℚ) - r) / Q)
  have hb' := Int.ceil_lt_add_one (((b : ℚ) - r) / Q)
  have heq : ((b : ℚ) - a) / Q = ((b : ℚ) - r) / Q - ((a : ℚ) - r) / Q := by ring
  rw [heq,abs_le]
  constructor <;> linarith

theorem count_error_length (a b Q r : ℤ) (hQ : 0 < Q) (hab : a ≤ b) :
    |((residueClass a b Q r).card : ℝ) - ((b : ℝ) - a) / Q| ≤ 1 := by
  have h := count_error_rat a b Q r hQ hab
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hh
  exact hh

theorem count_error (a b Q r : ℤ) (hQ : 0 < Q) :
    |((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ) / Q| ≤ 1 := by
  by_cases hab : a ≤ b
  · have hc : ((Ico a b).card : ℤ) = b-a := by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hc
    push_cast at hcast
    rw [hcast]
    exact count_error_length a b Q r hQ hab
  · have he : Ico a b = (∅ : Finset ℤ) := Ico_eq_empty_of_le (le_of_not_ge hab)
    simp [residueClass,he]

end Erdos66Dependency.SingleResidueCount



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem integerCRTResidues_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    (integerCRTResidues m hcop E).card = ∏ i,(E i).card := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  have hinj : Function.Injective (fun r : ZMod (∏ i,m i) => (r.val : ℤ)) := by
    intro r s he
    exact ZMod.val_injective _ (Int.ofNat_inj.mp he)
  rw [integerCRTResidues,Finset.card_image_of_injective _ hinj,crtResidues_card]

theorem integerCRTResidues_subset {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    integerCRTResidues m hcop E ⊆ Finset.Ico 0 (∏ i,m i : ℕ) := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  intro s hs
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _,by exact_mod_cast ZMod.val_lt r⟩

theorem emod_mem_integerCRTResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) (s : ℤ) :
    s % (∏ i,m i : ℕ) ∈ integerCRTResidues m hcop E ↔ ∀ i,(s : ZMod (m i)) ∈ E i := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  rw [← intCast_mem_crtResidues m hcop E s,← ZMod.val_intCast s]
  constructor
  · intro hs
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hs
    have heq : r = (s : ZMod (∏ i,m i)) := ZMod.val_injective _ (Int.ofNat_inj.mp he)
    rwa [← heq]
  · intro hs
    exact Finset.mem_image.mpr ⟨(s : ZMod (∏ i,m i)),hs,rfl⟩

theorem product_card_le_moduli {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (E : ∀ i,Finset (ZMod (m i))) (hm : ∀ i,0 < m i) :
    (∏ i,(E i).card) ≤ ∏ i,m i := by
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro i hi
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simpa only [ZMod.card] using Finset.card_le_univ (E i)

end ErdosInverseCRT



namespace Erdos66Dependency.ResidueLifts

open Finset SingleResidueCount

theorem lifts_eq_union (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    liftsOn (Ico a b) Q A = A.biUnion (residueClass a b Q) := by
  classical
  ext x
  simp only [liftsOn,mem_filter,mem_biUnion,residueClass]
  constructor
  · rintro ⟨hx,hA⟩
    exact ⟨x%Q,hA,hx,by unfold Int.ModEq; rw [Int.emod_emod]⟩
  · rintro ⟨r,hr,hx,hmod⟩
    have hrange := mem_Ico.mp (hA hr)
    have he : x%Q=r := by simpa only [Int.ModEq,Int.emod_eq_of_lt hrange.1 hrange.2] using hmod
    exact ⟨hx,he ▸ hr⟩

theorem classes_disjoint (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    (A : Set ℤ).PairwiseDisjoint (residueClass a b Q) := by
  intro r hr s hs hne
  apply Finset.disjoint_left.mpr
  intro x hxr hxs
  have hrange := mem_Ico.mp (hA hr)
  have hsrange := mem_Ico.mp (hA hs)
  have hmodr := (mem_filter.mp hxr).2
  have hmods := (mem_filter.mp hxs).2
  have heqR : x%Q=r := by simpa only [Int.ModEq,Int.emod_eq_of_lt hrange.1 hrange.2] using hmodr
  have heqS : x%Q=s := by simpa only [Int.ModEq,Int.emod_eq_of_lt hsrange.1 hsrange.2] using hmods
  exact hne (heqR.symm.trans heqS)

theorem count_eq_sum (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    (liftsOn (Ico a b) Q A).card = ∑ r ∈ A, (residueClass a b Q r).card := by
  rw [lifts_eq_union a b Q A hA,card_biUnion (classes_disjoint a b Q A hA)]

theorem count_error (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q) (hA : A ⊆ Ico 0 Q) :
    |((liftsOn (Ico a b) Q A).card : ℝ) - ((Ico a b).card : ℝ) * A.card / Q| ≤ A.card := by
  rw [count_eq_sum a b Q A hA,Nat.cast_sum]
  have heq : (∑ r ∈ A, ((residueClass a b Q r).card : ℝ)) - ((Ico a b).card : ℝ)*A.card/Q =
      ∑ r ∈ A, (((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ)/Q) := by
    rw [sum_sub_distrib]
    simp only [sum_const,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ∑ r ∈ A, |((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ)/Q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ A, (1:ℝ) := sum_le_sum (fun r _ => SingleResidueCount.count_error a b Q r hQ)
    _ = (A.card:ℝ) := by simp

lemma card_Ico_real {a b : ℤ} (hab : a ≤ b) : ((Ico a b).card : ℝ) = (b:ℝ)-a := by
  have h : ((Ico a b).card : ℤ) = b-a := by rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  have hh := congrArg (fun z : ℤ => (z:ℝ)) h
  push_cast at hh
  exact hh

theorem count_error_length (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q)
    (hA : A ⊆ Ico 0 Q) (hab : a ≤ b) :
    |((liftsOn (Ico a b) Q A).card : ℝ) - ((b:ℝ)-a)*A.card/Q| ≤ A.card := by
  simpa only [card_Ico_real hab] using count_error a b Q A hQ hA

end Erdos66Dependency.ResidueLifts



namespace ErdosInverseCRT
open Erdos66Dependency
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem crtSlopes_eq_lifts {ι : Type*} [Fintype ι] (a b : ℤ) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    crtSlopes a b m E = ResidueLifts.liftsOn (Finset.Ico a b) (∏ i,m i : ℕ) (integerCRTResidues m hcop E) := by
  ext s
  simp only [crtSlopes,ResidueLifts.liftsOn,Finset.mem_filter,emod_mem_integerCRTResidues m hcop E hN s]

theorem crt_interval_count_upper {ι : Type*} [Fintype ι] (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    ((crtSlopes a b m E).card : ℝ) ≤
      ((b : ℝ)-(a : ℝ))*((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,m i : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  have hQ : (0 : ℤ) < (∏ i,m i : ℕ) := by exact_mod_cast hN
  have hh := ResidueLifts.count_error_length a b (∏ i,m i : ℕ) (integerCRTResidues m hcop E)
    hQ (integerCRTResidues_subset m hcop E hN) hab
  rw [← crtSlopes_eq_lifts a b m hcop E hN,integerCRTResidues_card m hcop E hN] at hh
  have hup := (abs_le.mp hh).2
  push_cast at hup ⊢
  linarith

theorem crt_initial_count_upper {ι : Type*} [Fintype ι] (p : ℕ) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    ((crtSlopes 0 p m E).card : ℝ) ≤
      (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,m i : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero] using
    crt_interval_count_upper 0 p (Int.natCast_nonneg p) m hcop E hN

end ErdosInverseCRT



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem mem_affineResidues {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) (s : R) :
    s ∈ affineResidues c b E ↔ (c : R)*s+b ∈ E := by
  constructor
  · intro hs
    obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hs
    have hh : (c : R)*s+b = t := by
      rw [← he]
      exact (affineEquiv c b).apply_symm_apply t
    rwa [hh]
  · intro hs
    exact Finset.mem_map.mpr ⟨(c : R)*s+b,hs,(affineEquiv c b).symm_apply_apply s⟩

theorem affineResidues_card {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) :
    (affineResidues c b E).card = E.card := Finset.card_map _

theorem source_edge_class_affine {R : Type*} [CommRing R] (p q : Rˣ) (a b s : R) :
    (a-b-(q : R)*s)*(↑((p*q)⁻¹) : R) =
      (↑(-(p⁻¹)) : R)*s+(a-b)*(↑((p*q)⁻¹) : R) := by
  have hc : (q : R)*(↑((p*q)⁻¹) : R) = (↑(p⁻¹) : R) := by
    change (↑(q*(p*q)⁻¹) : R) = (↑(p⁻¹) : R)
    congr 1
    simp [mul_inv_rev]
  calc
    _ = (a-b)*(↑((p*q)⁻¹) : R)-s*((q : R)*(↑((p*q)⁻¹) : R)) := by ring
    _ = _ := by rw [hc];simp only [Units.val_neg] <;> ring

end ErdosInverseCRT



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ParentProgression
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem parent_start_mod_p (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) :
    Nat.ModEq p (b+q*parentSlope p q hqp a b) a := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [Nat.cast_add,Nat.cast_mul,parentSlope,ZMod.natCast_zmod_val]
  have hu : (q : ZMod p)*(↑((ZMod.unitOfCoprime q hqp)⁻¹) : ZMod p) = 1 := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime q hqp).mul_inv
  calc
    (b : ZMod p)+(q : ZMod p)*(((a : ZMod p)-(b : ZMod p))*↑((ZMod.unitOfCoprime q hqp)⁻¹)) =
      (b : ZMod p)+((a : ZMod p)-(b : ZMod p))*((q : ZMod p)*↑((ZMod.unitOfCoprime q hqp)⁻¹)) := by ring
    _ = _ := by rw [hu];ring

end ErdosInverseHits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AugmentedCRTCell
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem augmented_coprime {ι : Type*} (M0 : ℕ) (u : ι → ℕ)
    (h0 : ∀ i,Nat.Coprime M0 (u i)) (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    Pairwise (fun i j => Nat.Coprime (augmentedModuli M0 u i) (augmentedModuli M0 u j)) := by
  rintro (_|i) (_|j) hne
  · exact False.elim (hne rfl)
  · exact h0 j
  · exact (h0 i).symm
  · exact hu (fun h => hne (congrArg Option.some h))

theorem augmented_product {ι : Type*} [Fintype ι] (M0 : ℕ) (u : ι → ℕ) :
    (∏ j : Option ι,augmentedModuli M0 u j) = M0*∏ i,u i := by
  simp only [Fintype.prod_option,augmentedModuli]

theorem cell_card_product {ι : Type*} [Fintype ι] (M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    (∏ j : Option ι,(cellResidues M0 u v c b E j).card) = ∏ i,(E i).card := by
  rw [Fintype.prod_option]
  have hbase : (cellResidues M0 u v c b E none).card = 1 := Finset.card_singleton v
  rw [hbase,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  exact affineResidues_card (c i) (b i) (E i)

theorem slopeCell_eq_crtSlopes {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    slopeCell p M0 u v c b E = crtSlopes 0 p (augmentedModuli M0 u) (cellResidues M0 u v c b E) := by
  ext s
  simp only [slopeCell,crtSlopes,Finset.mem_filter]
  apply and_congr_right
  intro _hs
  constructor
  · rintro ⟨hv,hE⟩ j
    cases j with
    | none => exact Finset.mem_singleton.mpr hv
    | some i => exact (mem_affineResidues (c i) (b i) (E i) (s : ZMod (u i))).mpr (hE i)
  · intro h
    exact ⟨Finset.mem_singleton.mp (h none),fun i => (mem_affineResidues (c i) (b i) (E i) (s : ZMod (u i))).mp (h (some i))⟩

theorem slopeCell_card_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i)))
    (hM : 0 < M0) (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((slopeCell p M0 u v c b E).card : ℝ) ≤
      (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  have hN : 0 < ∏ j : Option ι,augmentedModuli M0 u j := by
    rw [augmented_product]
    exact Nat.mul_pos hM (Finset.prod_pos (fun i _ => hU i))
  have hh := crt_initial_count_upper p (augmentedModuli M0 u) (augmented_coprime M0 u h0 hu)
    (cellResidues M0 u v c b E) hN
  rw [← slopeCell_eq_crtSlopes,augmented_product,cell_card_product] at hh
  exact hh

end ErdosInverseCRT

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SlopeCellPartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem sampledSlopes_partition {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    sampledSlopes p M0 u c b E = Finset.univ.biUnion (fun v : ZMod M0 => slopeCell p M0 u v c b (E v)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsp,hE⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_biUnion.mpr ⟨(s : ZMod M0),Finset.mem_univ _,Finset.mem_filter.mpr ⟨hsp,rfl,hE⟩⟩
  · intro hs
    obtain ⟨v,hv,hcell⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨hsp,hsv,hE⟩ := Finset.mem_filter.mp hcell
    apply Finset.mem_filter.mpr
    refine ⟨hsp,?_⟩
    rwa [hsv]

theorem slopeCells_disjoint {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) {v w : ZMod M0} (hne : v ≠ w) :
    Disjoint (slopeCell p M0 u v c b (E v)) (slopeCell p M0 u w c b (E w)) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact hne ((Finset.mem_filter.mp hs).2.1.symm.trans (Finset.mem_filter.mp ht).2.1)

theorem sampledSlopes_card {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    (sampledSlopes p M0 u c b E).card = ∑ v : ZMod M0,(slopeCell p M0 u v c b (E v)).card := by
  rw [sampledSlopes_partition,Finset.card_biUnion]
  intro v hv w hw hne
  exact slopeCells_disjoint p M0 u c b E hne

end ErdosInverseCRT

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceEdgeClasses
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem product_density {ι : Type*} [Fintype ι] (u : ι → ℕ) (E : ∀ i,Finset (ZMod (u i))) :
    ((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,u i : ℕ) = ∏ i,((E i).card : ℝ)/(u i : ℝ) := by
  push_cast
  rw [Finset.prod_div_distrib]

theorem slopeCell_normalized_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i)))
    (hM : 0 < M0) (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((slopeCell p M0 u v c b E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∏ i,((E i).card : ℝ)/(u i : ℝ))+((∏ i,u i : ℕ) : ℝ) := by
  have hcR : ((∏ i,(E i).card : ℕ) : ℝ) ≤ ((∏ i,u i : ℕ) : ℝ) :=
    Nat.cast_le.mpr (product_card_le_moduli u E hU)
  calc
    _ ≤ (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) :=
      slopeCell_card_upper p M0 u v c b E hM hU h0 hu
    _ ≤ (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,u i : ℕ) : ℝ) :=
      add_le_add le_rfl hcR
    _ = (p : ℝ)/(M0 : ℝ)*(((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,u i : ℕ))+((∏ i,u i : ℕ) : ℝ) := by
      push_cast
      ring
    _ = _ := by rw [product_density]

theorem sampledSlopes_card_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i)))
    (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((sampledSlopes p M0 u c b E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i,((E v i).card : ℝ)/(u i : ℝ))+
        (M0 : ℝ)*((∏ i,u i : ℕ) : ℝ) := by
  have hM : 0 < M0 := Nat.pos_of_ne_zero (NeZero.ne M0)
  calc
    _ = ∑ v : ZMod M0,((slopeCell p M0 u v c b (E v)).card : ℝ) := by
      exact_mod_cast sampledSlopes_card p M0 u c b E
    _ ≤ ∑ v : ZMod M0,((p : ℝ)/(M0 : ℝ)*(∏ i,((E v i).card : ℝ)/(u i : ℝ))+((∏ i,u i : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun v _ => slopeCell_normalized_upper p M0 u v c b (E v) hM hU h0 hu)
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,ZMod.card]

end ErdosInverseCRT

end

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem sourceEdgeResidue_eq_affine (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b s : ℤ) : sourceEdgeResidue p q u hp hq a b s =
      (sourceCoefficient p u hp : ZMod u)*(s : ZMod u)+sourceShift p q u hp hq a b := by
  have hh := source_edge_class_affine (ZMod.unitOfCoprime p hp) (ZMod.unitOfCoprime q hq)
    (a : ZMod u) (b : ZMod u) (s : ZMod u)
  simpa only [sourceEdgeResidue,sourceCoefficient,sourceShift,ZMod.coe_unitOfCoprime] using hh

theorem sourceTestedSlopes_eq_sampledSlopes {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    sourceTestedSlopes p q0 M0 u hp hq a b0 E = sampledSlopes p M0 u
      (fun i => sourceCoefficient p (u i) (hp i))
      (fun i => sourceShift p q0 (u i) (hp i) (hq i) (a (u i)) b0) E := by
  ext s
  simp only [sourceTestedSlopes,sampledSlopes,Finset.mem_filter,sourceEdgeResidue_eq_affine]

end ErdosInverseCRT

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

end ErdosInverseEuler

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

namespace ErdosInverseCells
open ErdosInverseHits ErdosGeometricValueCells
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem cofactorHit_eq (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    cofactorHit q a = primeHitRepresentative q hq a := by simp only [cofactorHit,dite_eq_left hq]

theorem cofactorHit_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ cofactorHit q a ∧ cofactorHit q a ≤ q ∧
      ∀ p ∈ q.primeFactors,cofactorHit q a%p = a p%p := by
  rw [cofactorHit_eq q hq a]
  have hh := primeHitRepresentative_spec q hq a
  exact ⟨hh.1,hh.2.1,(hh.2.2 _).mpr (Nat.ModEq.refl _)⟩

end ErdosInverseCells

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells

theorem refinementLabel_card (W : ℕ) [NeZero W] : Fintype.card (RefinementLabel W) = W^2 := by
  simp only [RefinementLabel,Fintype.card_prod,ZMod.card]
  ring

theorem mem_refinementCell (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) (i : RefinementLabel W) (q : ℕ) :
    q ∈ refinementCell C a W i ↔ q ∈ C ∧ refinementLabel a W q = i :=
  mem_labelFiber C (refinementLabel a W) i q

end ErdosInverseRefinement

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

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SourcePrimeSampleBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem prime_sample_coprime (U : Finset ℕ) (hU : ∀ u ∈ U,Nat.Prime u) (h : ℕ) (sample : Fin h ↪ U) :
    Pairwise (fun i j => Nat.Coprime (sample i).val (sample j).val) := by
  intro i j hij
  apply (Nat.coprime_primes (hU _ (sample i).property) (hU _ (sample j).property)).mpr
  intro he
  exact hij (sample.injective (Subtype.ext he))

theorem sourceTestedSlopes_card_upper {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i)))
    (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((sourceTestedSlopes p q0 M0 u hp hq a b0 E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i,((E v i).card : ℝ)/(u i : ℝ))+
        (M0 : ℝ)*((∏ i,u i : ℕ) : ℝ) := by
  rw [sourceTestedSlopes_eq_sampledSlopes]
  exact sampledSlopes_card_upper p M0 u _ _ E hU h0 hu

theorem distinct_prime_sample_slope_bound (U : Finset ℕ) (hU : ∀ u ∈ U,Nat.Prime u)
    (h : ℕ) (sample : Fin h ↪ U) (p q0 M0 : ℕ) [NeZero M0]
    (hp : ∀ u ∈ U,Nat.Coprime p u) (hq : ∀ u ∈ U,Nat.Coprime q0 u)
    (h0 : ∀ u ∈ U,Nat.Coprime M0 u) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i : Fin h,Finset (ZMod (sample i).val)) :
    ((sourceTestedSlopes p q0 M0 (fun i => (sample i).val)
      (fun i => hp _ (sample i).property) (fun i => hq _ (sample i).property) a b0 E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i : Fin h,((E v i).card : ℝ)/((sample i).val : ℝ))+
        (M0 : ℝ)*((∏ i : Fin h,(sample i).val : ℕ) : ℝ) := by
  exact sourceTestedSlopes_card_upper p q0 M0 _ _ _ a b0 E
    (fun i => (hU _ (sample i).property).pos) (fun i => h0 _ (sample i).property)
    (prime_sample_coprime U hU h sample)

end ErdosInverseCRT

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceSquareScale
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
namespace ErdosSourcePolynomial
open ErdosInverseBoxHeight

theorem sourceZ_ge_one {z : ℝ} (hL : 1 ≤ Real.log z) : 1 ≤ sourceZ z := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (zero_le_one.trans hL) (Real.log_nonneg hL)

theorem square_scale_of_root_height {z Sq R : ℝ} (hSq : 0 ≤ Sq) (hR : 1 ≤ R)
    (hL : 1 ≤ Real.log z) (hheight : 2*Sq*R^2*(sourceZ z)^20 ≤ z^3) : Sq ≤ z^3 := by
  have hR2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hZ20 : 1 ≤ (sourceZ z)^20 := one_le_pow₀ (sourceZ_ge_one hL)
  have hm : 1 ≤ R^2*(sourceZ z)^20 := one_le_mul_of_one_le_of_one_le hR2 hZ20
  have hf : 1 ≤ 2*(R^2*(sourceZ z)^20) := by linarith
  calc
    Sq = Sq*1 := by ring
    _ ≤ Sq*(2*(R^2*(sourceZ z)^20)) := mul_le_mul_of_nonneg_left hf hSq
    _ = 2*Sq*R^2*(sourceZ z)^20 := by ring
    _ ≤ z^3 := hheight

theorem uniform_source_square_scale (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ Sq R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ Sq/q → Sq/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      1 ≤ R → R ≤ z^((1 : ℝ)/100) → 0 ≤ xi → xi ≤ 1 → Sq ≤ z^3 := by
  filter_upwards [uniform_box_height C hC,source_B_bounds,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2 : ℝ)] with z hheight hB hL hz
  refine ⟨hz,hL,?_⟩
  intro Sq R p q xi hp hq hpq hSqratio hinfl hR hRhi hxi0 hxi1
  have hSq : 0 ≤ Sq := hq.le.trans ((one_le_div hq).mp hSqratio)
  have hqz := source_cofactor_le_square hL hp hq.le hpq
  have hh := hheight.2 Sq R (sourceB z) xi q hSq (zero_le_one.trans hR)
    hB.2.1 hB.2.2 hxi0 hxi1 hq hqz hinfl hRhi
  exact square_scale_of_root_height hSq hR hL hh

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualUnalignedIncidence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph

theorem uniform_actual_unaligned_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (l : PrimitiveIntegerLine) (r : InterceptReduction l)
        (X : Finset (ℤ × ℤ)), (∀ v ∈ X,l.Contains v) → (∀ v ∈ X,InSquare S v) →
        Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S ≤ z^3 → z^((93 : ℝ)/100) ≤ (X.card : ℝ) →
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        (∑ p ∈ unalignedPrimes (primeBin R xi) a r,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
          eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  classical
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count heta)
  have hs := uniform_normalized_collision (3/alpha) eta eps (by positivity) heta heps
  filter_upwards [hs,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0] with z hz hzR
  refine ⟨hz.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin
  have hb := hR0 R (hzR.trans hRlo)
  have hR : 1 < R := by linarith [hb.1]
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hxipos : 0 ≤ xi := heta.le.trans hxi
  let P := primeBin R xi
  let U := unalignedPrimes P a r
  have hsub : U ⊆ P := Finset.filter_subset _ _
  have hprime (p : ℕ) (hp : p ∈ P) : Nat.Prime p := ((mem_primeBin hRpos.le hxipos p).mp hp).1
  have hplarge (p : ℕ) (hp : p ∈ P) : z^alpha ≤ (p : ℝ) :=
    hRlo.trans (((mem_primeBin hRpos.le hxipos p).mp hp).2.1.le)
  have hcount : eta*R/(4*Real.log R) ≤ (P.card : ℝ) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxi hRpos.le)
      (by positivity : 0 ≤ 4*Real.log R)).trans
    exact (hb.2 xi hxi hxi1).1
  have hcollision := actual_collision_bound r U X a T hline
    (fun p hp => hprime p (hsub hp))
    (fun _ hp => (Finset.mem_filter.mp hp).2.1)
    (fun _ hp => (Finset.mem_filter.mp hp).2.2)
    hinj S z alpha hbox hz.1 halpha (fun p hp => hplarge p (hsub hp)) hS
  have hKU : (∑ p ∈ U,((T p).card : ℝ)) ≤ ∑ p ∈ P,((T p).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hI : (∑ p ∈ U,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤ (P.card : ℝ)*(X.card : ℝ) :=
    (total_incidence_le_product U X a T).trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _))
  exact hz.2 _ _ R _ _ hR hRhi hN hcount (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    hcollision (hKU.trans hthin) hI

end ErdosSourceCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_IgnoredDenominatorPrimes
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosInverseBoxHeight

theorem ignoredPrimes_card_le (P : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P,Nat.Prime p) (z alpha : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hheight : (d : ℝ) ≤ z) :
    ((ignoredPrimes P d).card : ℝ) ≤ 1/alpha := by
  have he : ignoredPrimes P d = dividingPrimes P (d : ℤ) := by
    classical
    ext p
    simp only [ignoredPrimes,dividingPrimes,Finset.mem_filter,Int.natCast_dvd_natCast]
  rw [he]
  apply dividingPrimes_card_bound P (d : ℤ) (by exact_mod_cast hd.ne') hP z alpha 1 hz ha hlarge
  simpa only [Int.cast_natCast,abs_of_nonneg (show (0 : ℝ) ≤ d from Nat.cast_nonneg d),Real.rpow_one] using hheight

theorem source_denominator_le_z {z R Z d : ℝ} (hz : 1 < z) (_hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hd : d ≤ R*Z^10) : d ≤ z := by
  have hz0 : 0 < z := by linarith
  have hZ10 : Z^10 ≤ z^((10 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^10 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  calc
    d ≤ R*Z^10 := hd
    _ ≤ z^((1 : ℝ)/100)*z^((10 : ℝ)/100) := by gcongr
    _ = z^((11 : ℝ)/100) := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ z := by
      have hh := Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (11 : ℝ)/100 ≤ 1)
      simpa only [Real.rpow_one] using hh

end ErdosSourceCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonstructuredCounts
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosSourceLineBudget
open ErdosRichLine

theorem source_line_heights (l : PrimitiveIntegerLine) (S R Z N : ℝ)
    (hS : 0 ≤ S) (hR : 0 < R) (hZ : 0 < Z) (hN : 0 < N)
    (hrich : S/(R*Z^6) < N) (hd : (l.denominator : ℝ) ≤ 2*S/N)
    (ha : |(l.slope : ℝ)| ≤ 2*S/N) (hb : |(l.intercept : ℝ)| ≤ 4*S^2/N) :
    (l.denominator : ℝ) ≤ 2*R*Z^6 ∧ |(l.slope : ℝ)| ≤ 2*R*Z^6 ∧
      |(l.intercept : ℝ)| ≤ 4*S*R*Z^6 := by
  have hmul : S < N*(R*Z^6) := (div_lt_iff₀ (by positivity : 0 < R*Z^6)).mp hrich
  have hratio : S/N ≤ R*Z^6 := (div_le_iff₀ hN).mpr (by nlinarith)
  have htwo : 2*S/N ≤ 2*R*Z^6 := by
    calc
      _ = 2*(S/N) := by ring
      _ ≤ 2*(R*Z^6) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = _ := by ring
  have hfour : 4*S^2/N ≤ 4*S*R*Z^6 := by
    calc
      _ = (4*S)*(S/N) := by ring
      _ ≤ (4*S)*(R*Z^6) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  exact ⟨hd.trans htwo,ha.trans htwo,hb.trans hfour⟩

theorem source_line_height_slack (l : PrimitiveIntegerLine) (S R Z : ℝ)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hZ : 2 ≤ Z)
    (hd : (l.denominator : ℝ) ≤ 2*R*Z^6) (ha : |(l.slope : ℝ)| ≤ 2*R*Z^6)
    (hb : |(l.intercept : ℝ)| ≤ 4*S*R*Z^6) :
    (l.denominator : ℝ) ≤ R*Z^10 ∧ |(l.slope : ℝ)| ≤ R*Z^10 ∧
      |(l.intercept : ℝ)| ≤ S*R*Z^10 := by
  have hZ0 : 0 ≤ Z := by linarith
  have hfour : 4 ≤ Z^4 := by nlinarith [sq_nonneg (Z^2-2)]
  have htwo : 2*R*Z^6 ≤ R*Z^10 := by
    nlinarith [mul_nonneg (mul_nonneg hR (pow_nonneg hZ0 6)) (show 0 ≤ Z^4-2 by linarith)]
  have hfour' : 4*S*R*Z^6 ≤ S*R*Z^10 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hS hR) (pow_nonneg hZ0 6)) (sub_nonneg.mpr hfour)]
  exact ⟨hd.trans htwo,ha.trans htwo,hb.trans hfour'⟩

end ErdosSourceLineBudget

end

section

namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine ErdosInversePrimeBin ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem nonstructured_richness_implies_polynomial_richness (R xi c S Z cp : ℝ)
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v : ℤ × ℤ)
    (h : c*((primeBin R xi).card : ℝ) ≤
      ((nonstructuredPrimes (primeBin R xi) a T S R Z cp v).card : ℝ)) :
    ErdosSourceLineBudget.RichPoint R xi c (fun p => T p.val) (fun p => a p.val) v := by
  let I := nonstructuredPrimes (primeBin R xi) a T S R Z cp v
  have hIP : I ⊆ primeBin R xi := Finset.filter_subset _ _
  refine ⟨I,hIP,h,?_⟩
  intro p
  exact (Finset.mem_filter.mp p.property).2.1

theorem contains_nat_abscissa (l : PrimitiveIntegerLine) (v : ℤ × ℤ)
    (h0 : 0 ≤ (v.1 : ℝ)) (hv : l.Contains v) : l.Contains ((v.1.toNat : ℤ),v.2) := by
  have hv0 : 0 ≤ v.1 := by exact_mod_cast h0
  have he := Int.toNat_of_nonneg hv0
  simpa only [he] using hv

end ErdosInverseStructured

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosInverseBoxHeight

theorem uniform_actual_ignored_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ R*(sourceZ z)^10 →
        ∀ (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ),
          (∑ p ∈ ignoredPrimes (primeBin R xi) d,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
            eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  let M : ℕ := ⌈(1/alpha)/eps⌉₊
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_many heta M)
  filter_upwards [sourceZ_le_small_power,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0] with z hz hzR
  refine ⟨hz.1,?_⟩
  intro R xi hRlo hRhi hxi hxi1 d hd hdheight X a T
  have hb := hR0 R (hzR.trans hRlo)
  have hRpos : 0 < R := by linarith [hb.1]
  have hxipos : 0 ≤ xi := heta.le.trans hxi
  have hheight := source_denominator_le_z hz.1 hRpos.le hz.2.1.le hRhi hz.2.2 hdheight
  have hprime (p : ℕ) (hp : p ∈ primeBin R xi) : Nat.Prime p :=
    ((mem_primeBin hRpos.le hxipos p).mp hp).1
  have hlarge (p : ℕ) (hp : p ∈ primeBin R xi) : z^alpha ≤ (p : ℝ) :=
    hRlo.trans (((mem_primeBin hRpos.le hxipos p).mp hp).2.1.le)
  have hcard := ignoredPrimes_card_le (primeBin R xi) d hd hprime z alpha hz.1 halpha hlarge hheight
  have hM : (M : ℝ) ≤ ((primeBin R xi).card : ℝ) := by exact_mod_cast hb.2 xi hxi hxi1
  have hceil : (1/alpha)/eps ≤ (M : ℝ) := Nat.le_ceil _
  have hsmall : 1/alpha ≤ eps*((primeBin R xi).card : ℝ) := by
    have hh := (div_le_iff₀ heps).mp (hceil.trans hM)
    nlinarith
  calc
    _ ≤ ((ignoredPrimes (primeBin R xi) d).card : ℝ)*(X.card : ℝ) :=
      total_incidence_le_product _ _ _ _
    _ ≤ (1/alpha)*(X.card : ℝ) := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)

end ErdosSourceCollision

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseBoxHeight ErdosConvexGraph

theorem uniform_actual_bad_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (l : PrimitiveIntegerLine) (r : InterceptReduction l)
        (X : Finset (ℤ × ℤ)), (∀ v ∈ X,l.Contains v) → (∀ v ∈ X,InSquare S v) →
        Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S ≤ z^3 → z^((93 : ℝ)/100) ≤ (X.card : ℝ) →
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        (l.denominator : ℝ) ≤ R*(sourceZ z)^10 →
        (∑ p ∈ unalignedPrimes (primeBin R xi) a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
          (∑ p ∈ ignoredPrimes (primeBin R xi) l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
            eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  filter_upwards [uniform_actual_unaligned_incidence eta alpha (eps/2) heta halpha (by positivity),
    uniform_actual_ignored_incidence eta alpha (eps/2) heta halpha (by positivity)] with z hu hi
  refine ⟨hu.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin hden
  have hU := hu.2 R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin
  have hI := hi.2 R xi hRlo hRhi hxi hxi1 l.denominator l.denominator_pos hden X a T
  linarith

end ErdosSourceCollision

end

section

namespace ErdosInverseStructured
open ErdosLineCollision
attribute [local instance] Classical.propDecidable

theorem nonstructured_double_count (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp : ℝ) :
    (∑ v ∈ X,((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) =
      ∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ) := by
  classical
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (NonstructuredIncidence P a T S R Z cp) (s := X) (t := P)
  change (∑ v ∈ X,((P.filter (NonstructuredIncidence P a T S R Z cp v)).card : ℝ)) =
    ∑ p ∈ P,((X.filter (fun v => NonstructuredIncidence P a T S R Z cp v p)).card : ℝ)
  exact_mod_cast hh

theorem nonstructuredPoints_subset_incident (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp : ℝ) (p : ℕ) :
    nonstructuredPoints P X a T S R Z cp p ⊆ incidentPoints X (a p) p (T p) := by
  intro v hv
  obtain ⟨hvX,hinc,_hnon⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvX,hinc⟩

theorem nonstructured_total_lower (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp c : ℝ)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) :
    c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ) := by
  rw [← nonstructured_double_count]
  calc
    _ = ∑ _v ∈ X,c*(P.card : ℝ) := by simp <;> ring
    _ ≤ _ := Finset.sum_le_sum hrich

theorem all_incidence_lower_of_nonstructured_richness (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp c : ℝ)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) :
    c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ) := by
  apply (nonstructured_total_lower P X a T S R Z cp c hrich).trans
  apply Finset.sum_le_sum
  intro p hp
  exact Nat.cast_le.mpr (Finset.card_le_card (nonstructuredPoints_subset_incident P X a T S R Z cp p))

end ErdosInverseStructured

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SampleWitnessAverage
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem many_large_weights {α : Type*} (A : Finset α) (f : α → ℝ) (beta : ℝ)
    (hb : 0 ≤ beta) (hf : ∀ a ∈ A,f a ≤ 1) (hmean : beta*(A.card : ℝ) ≤ ∑ a ∈ A,f a) :
    (beta/2)*(A.card : ℝ) ≤ ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ) := by
  have hup : (∑ a ∈ A,f a) ≤
      ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ)+(A.card : ℝ)*(beta/2) := by
    calc
      _ ≤ ∑ a ∈ A,((if beta/2 ≤ f a then (1 : ℝ) else 0)+beta/2) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hh : beta/2 ≤ f a
        · rw [ite_eq_left hh]
          linarith [hf a ha]
        · rw [ite_eq_right hh,zero_add]
          exact (lt_of_not_ge hh).le
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_boole]
        simp
  linarith

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OriginalCofactorPoints
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem selected_pairs_card_by_rows (P C U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) :
    (selectedPairs (P.product C) U witness h s).card = ∑ q ∈ C,(selectedRow P U witness h s q).card := by
  calc
    _ = ∑ p ∈ P,∑ q ∈ C,if (∀ i : Fin h,witness (p,q) (s i).val) then (1 : ℕ) else 0 := by
      simp only [selectedPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
      exact Finset.sum_product P C (fun v : ℕ × ℕ => if (∀ i : Fin h,witness v (s i).val) then (1 : ℕ) else 0)
    _ = ∑ q ∈ C,∑ p ∈ P,if (∀ i : Fin h,witness (p,q) (s i).val) then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by simp only [selectedRow,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem rowReward_bounds (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) (hP : 0 < P.card) :
    0 ≤ rowReward P U witness h s q ∧ rowReward P U witness h s q ≤ 1 := by
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP
  refine ⟨div_nonneg (Nat.cast_nonneg _) hPpos.le,?_⟩
  apply (div_le_iff₀ hPpos).mpr
  simpa only [one_mul] using (show ((selectedRow P U witness h s q).card : ℝ) ≤ P.card by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _))

theorem rowReward_sum (P C U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (hP : 0 < P.card) (hC : 0 < C.card) :
    (∑ q ∈ C,rowReward P U witness h s q) = selectedFraction (P.product C) U witness h s*(C.card : ℝ) := by
  have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hc : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  unfold rowReward selectedFraction
  rw [← Finset.sum_div,selected_pairs_card_by_rows,Nat.cast_sum,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  field_simp

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem richCofactors_subset (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) : richCofactors D P U witness h s gamma ⊆ D :=
  Finset.filter_subset _ _

theorem richCofactors_card_lower (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) (hg : 0 ≤ gamma) (hP : 0 < P.card)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    (gamma/8)*(D.card : ℝ) ≤ ((richCofactors D P U witness h s gamma).card : ℝ) := by
  have hh := many_large_weights D (rowReward P U witness h s) (gamma/4) (by positivity)
    (fun q _ => (rowReward_bounds P U witness h s q hP).2) hdense
  simpa only [div_div,show (4 : ℝ)*2 = 8 by norm_num,richCofactors] using hh

theorem richCofactor_row_card (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) (hP : 0 < P.card) (q : ℕ)
    (hq : q ∈ richCofactors D P U witness h s gamma) :
    (gamma/8)*(P.card : ℝ) ≤ ((selectedRow P U witness h s q).card : ℝ) := by
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hh := (Finset.mem_filter.mp hq).2
  exact (le_div_iff₀ hp).mp hh

theorem richCofactors_source_size (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma S Z : ℝ) (hg : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hP : 0 < P.card) (hD : S/Z^3 ≤ (D.card : ℝ)) (hInv : 1/Z ≤ gamma/8)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    S/Z^4 ≤ ((richCofactors D P U witness h s gamma).card : ℝ) := by
  calc
    _ = (1/Z)*(S/Z^3) := by field_simp
    _ ≤ (gamma/8)*(S/Z^3) := mul_le_mul_of_nonneg_right hInv (by positivity)
    _ ≤ (gamma/8)*(D.card : ℝ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ _ := richCofactors_card_lower D P U witness h s gamma hg.le hP hdense

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosConvexGraph
attribute [local instance] Classical.decEq

theorem cofactorPoint_injective (a : ℕ → ℕ) : Function.Injective (cofactorPoint a) := by
  intro q r he
  have hh := congrArg Prod.fst he
  change (q : ℤ) = (r : ℤ) at hh
  exact_mod_cast hh

theorem cofactorPoints_card (D : Finset ℕ) (a : ℕ → ℕ) :
    (cofactorPoints D a).card = D.card :=
  Finset.card_image_of_injective D (cofactorPoint_injective a)

theorem cofactorPoints_x_injective (D : Finset ℕ) (a : ℕ → ℕ) :
    Set.InjOn Prod.fst (cofactorPoints D a : Set (ℤ × ℤ)) := by
  rintro v hv w hw he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hw
  have hqr : q = r := by
    change (q : ℤ) = (r : ℤ) at he
    exact_mod_cast he
  exact congrArg (cofactorPoint a) hqr

theorem cofactorPoints_square (D : Finset ℕ) (a : ℕ → ℕ) (S : ℝ)
    (hq : ∀ q ∈ D,Squarefree q ∧ (q : ℝ) ≤ S) :
    ∀ v ∈ cofactorPoints D a,InSquare S v := by
  intro v hv
  obtain ⟨q,hqD,rfl⟩ := Finset.mem_image.mp hv
  have hb := cofactorHit_spec q (hq q hqD).1 a
  have hbq : (cofactorHit q a : ℝ) ≤ q := by exact_mod_cast hb.2.1
  change (0 ≤ ((q : ℤ) : ℝ) ∧ ((q : ℤ) : ℝ) ≤ S) ∧
    (0 ≤ ((cofactorHit q a : ℤ) : ℝ) ∧ ((cofactorHit q a : ℤ) : ℝ) ≤ S)
  push_cast
  exact ⟨⟨Nat.cast_nonneg _,(hq q hqD).2⟩,⟨Nat.cast_nonneg _,hbq.trans (hq q hqD).2⟩⟩

theorem cofactorPoints_prime_hits (D : Finset ℕ) (a : ℕ → ℕ)
    (hq : ∀ q ∈ D,Squarefree q) :
    ∀ v ∈ cofactorPoints D a,∀ p ∈ v.1.toNat.primeFactors,
      (v.2 : ZMod p) = (a p : ZMod p) := by
  intro v hv
  obtain ⟨q,hqD,rfl⟩ := Finset.mem_image.mp hv
  intro p hp
  have hh := (cofactorHit_spec q (hq q hqD) a).2.2 p hp
  change ((cofactorHit q a : ℤ) : ZMod p) = (a p : ZMod p)
  rw [Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh

theorem rich_points_source_size (D P U : Finset ℕ) (a : ℕ → ℕ)
    (witness : (ℕ × ℕ) → ℕ → Prop) (h : ℕ) (s : ErdosInverseSampling.Sample U h)
    (gamma S Z : ℝ) (hg : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hP : 0 < P.card) (hD : S/Z^3 ≤ (D.card : ℝ)) (hInv : 1/Z ≤ gamma/8)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    S/Z^4 ≤ ((cofactorPoints (richCofactors D P U witness h s gamma) a).card : ℝ) := by
  rw [cofactorPoints_card]
  exact richCofactors_source_size D P U witness h s gamma S Z hg hS hZ hP hD hInv hdense

end ErdosInverseRefinement

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

namespace ErdosInverseSampleCost
open ErdosInverseSampling ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem slopes_card_le_primeCost (U : Finset ℕ) (hU : ∀ u ∈ U,u.Prime)
    (h M0 : ℕ) [NeZero M0] (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val))
    (s : Sample U h) (p q0 : ℕ) (hp : ∀ u ∈ U,p.Coprime u) (hq : ∀ u ∈ U,q0.Coprime u)
    (h0 : ∀ u ∈ U,M0.Coprime u) (a : ℕ → ℤ) (b0 : ℤ) :
    ((sourceTestedSlopes p q0 M0 (fun i => (s i).val)
      (fun i => hp _ (s i).property) (fun i => hq _ (s i).property) a b0
      (fun v i => E p v (s i))).card : ℝ) ≤ primeCost U h M0 E p s := by
  have hh := distinct_prime_sample_slope_bound U hU h s p q0 M0 hp hq h0 a b0 (fun v i => E p v (s i))
  simpa only [primeCost,Nat.cast_prod] using hh

theorem slopes_sum_le_totalCost (P U : Finset ℕ) (hU : ∀ u ∈ U,u.Prime)
    (h M0 : ℕ) [NeZero M0] (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val))
    (s : Sample U h) (hP : 0 < P.card) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (h0 : ∀ u ∈ U,M0.Coprime u) (q0 : ℕ) (hq : ∀ u ∈ U,q0.Coprime u)
    (a : ℕ → ℤ) (b0 : ℤ) :
    (∑ p : P,((sourceTestedSlopes p.val q0 M0 (fun i => (s i).val)
      (fun i => hp p.val p.property _ (s i).property) (fun i => hq _ (s i).property) a b0
      (fun v i => E p.val v (s i))).card : ℝ)) ≤
        (P.card : ℝ)*totalCost P U h M0 E s := by
  have hPnz : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  calc
    _ ≤ ∑ p : P,primeCost U h M0 E p.val s :=
      Finset.sum_le_sum (fun p _ => slopes_card_le_primeCost U hU h M0 E s p.val q0
        (hp p.val p.property) hq h0 a b0)
    _ = ∑ p ∈ P,primeCost U h M0 E p s := Finset.sum_coe_sort P (fun p : ℕ => primeCost U h M0 E p s)
    _ = _ := by unfold totalCost;field_simp

end ErdosInverseSampleCost

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseCRT ErdosInverseEuler
attribute [local instance] Classical.decEq

theorem smallModulus_coprime_largePrime (w : ℝ) (hw : 0 ≤ w) (u : ℕ)
    (hu : u.Prime) (hwu : w < (u : ℝ)) : (smallModulus w).Coprime u := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hh := LargePrimeDeletion.mem_cutoffPrimes.mp hp
  have hpw : (p : ℝ) ≤ w := (Nat.le_floor_iff hw).mp hh.2
  apply (Nat.coprime_primes hh.1 hu).mpr
  intro he
  subst p
  linarith

theorem actual_slopes_thin (Y : ℕ) (w Qplus R L : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hw : 0 ≤ w) (hR : 0 < R) (hP : 0 < P.card) (hU : ∀ u ∈ U,u.Prime)
    (huLarge : ∀ u ∈ U,w < (u : ℝ)) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (hcost : actualCost Y w Qplus R qInitial bInitial a delta P U h s ≤ 1/L^6) :
    let M0 := smallModulus w
    letI : NeZero M0 := ⟨(smallModulus_pos w).ne'⟩
    ∀ (qRef : ℕ) (bRef : ℤ) (hqRef : ∀ u ∈ U,qRef.Coprime u),
      (∑ p : P,((sourceTestedSlopes p.val qRef M0 (fun i => (s i).val)
        (fun i => hp p.val p.property _ (s i).property) (fun i => hqRef _ (s i).property)
        (fun u => (a u : ℤ)) bRef
        (fun v i => actualFamily Y w Qplus qInitial bInitial a delta U M0 p.val v (s i))).card : ℝ)) ≤
          (P.card : ℝ)*R/L^6 := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  dsimp only
  intro qRef bRef hqRef
  have h0 : ∀ u ∈ U,(smallModulus w).Coprime u :=
    fun u hu => smallModulus_coprime_largePrime w hw u (hU u hu) (huLarge u hu)
  have htot : totalCost P U h (smallModulus w)
      (actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w)) s ≤ R/L^6 := by
    have hh := (div_le_iff₀ hR).mp hcost
    calc
      _ ≤ (1/L^6)*R := hh
      _ = R/L^6 := by ring
  calc
    _ ≤ (P.card : ℝ)*totalCost P U h (smallModulus w)
        (actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w)) s :=
      slopes_sum_le_totalCost P U hU h (smallModulus w) _ s hP hp h0 qRef hqRef (fun u => (a u : ℤ)) bRef
    _ ≤ (P.card : ℝ)*(R/L^6) := mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg _)
    _ = _ := by ring

end ErdosInverseSampleCost

end

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

section

namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseCRT ErdosInverseEuler ErdosInverseHits ErdosInverseStructured
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem pointSlopes_thin (Y : ℕ) (w Qplus R L : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hw : 0 ≤ w) (hR : 0 < R) (hP : 0 < P.card) (hU : ∀ u ∈ U,u.Prime)
    (huLarge : ∀ u ∈ U,w < (u : ℝ)) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (hcost : actualCost Y w Qplus R qInitial bInitial a delta P U h s ≤ 1/L^6)
    (qRef : ℕ) (bRef : ℤ) (hqRef : ∀ u ∈ U,qRef.Coprime u) :
    (∑ p ∈ P,((pointSlopes Y w Qplus qInitial bInitial a delta P U h s hp qRef bRef hqRef p).card : ℝ)) ≤
      (P.card : ℝ)*R/L^6 := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  have hh := actual_slopes_thin Y w Qplus R L qInitial bInitial a delta P U h s hw hR hP hU huLarge hp hcost
    qRef bRef hqRef
  rw [← Finset.sum_coe_sort P (fun p : ℕ =>
    ((pointSlopes Y w Qplus qInitial bInitial a delta P U h s hp qRef bRef hqRef p).card : ℝ))]
  simpa only [pointSlopes,dite_eq_left (Subtype.property _)] using hh

theorem parentSlope_incidence (a : ℕ → ℕ) (T : ℕ → Finset ℤ) (p q : ℕ) [NeZero p]
    (hqp : q.Coprime p)
    (hs : (parentSlope p q hqp (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    SlopeIncidence (fun u => (a u : ℤ)) T (cofactorPoint a q) p := by
  refine ⟨(parentSlope p q hqp (a p) (cofactorHit q a) : ℤ),hs,?_⟩
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (parent_start_mod_p p q hqp (a p) (cofactorHit q a))
  simp only [Nat.cast_add,Nat.cast_mul] at he
  change ((cofactorHit q a : ℤ) : ZMod p) = ((a p : ℤ) : ZMod p)-
    ((parentSlope p q hqp (a p) (cofactorHit q a) : ℤ) : ZMod p)*((q : ℤ) : ZMod p)
  simp only [Int.cast_natCast]
  linear_combination he

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RefinedDiscardBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseCells

theorem refined_discard_bound (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) [NeZero W]
    (S Z gamma : ℝ) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hC : S/Z ≤ (C.card : ℝ)) (hW : (W : ℝ)^2 ≤ Z) (hInv : 1/Z ≤ gamma/8) :
    ((discardedPoints C (refinementLabel a W) (S/Z^3)).card : ℝ) ≤ (gamma/8)*(C.card : ℝ) := by
  have hh := discardedPoints_card_bound C (refinementLabel a W) (S/Z^3) (by positivity)
  rw [refinementLabel_card] at hh
  push_cast at hh
  calc
    _ ≤ (W : ℝ)^2*(S/Z^3) := hh
    _ ≤ Z*(S/Z^3) := mul_le_mul_of_nonneg_right hW (by positivity)
    _ = (1/Z)*(S/Z) := by field_simp
    _ ≤ (1/Z)*(C.card : ℝ) := mul_le_mul_of_nonneg_left hC (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hInv (Nat.cast_nonneg _)

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RefinementRewardMargin
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseCells
attribute [local instance] Classical.decEq

theorem dense_fiber_after_count_discard {ι : Type*} [Fintype ι]
    (C : Finset ℕ) (label : ℕ → ι) (tau rho eta d : ℝ) (hC : 0 < C.card) (heta : 0 ≤ eta)
    (hgap : eta+d < rho) (f : ℕ → ℝ) (hf : ∀ q ∈ C,f q ≤ 1)
    (hMass : rho*(C.card : ℝ) ≤ ∑ q ∈ C,f q)
    (hDiscard : ((discardedPoints C label tau).card : ℝ) ≤ d*(C.card : ℝ)) :
    ∃ i : ι,tau ≤ ((labelFiber C label i).card : ℝ) ∧
      eta*((labelFiber C label i).card : ℝ) < ∑ q ∈ labelFiber C label i,f q := by
  classical
  by_contra hno
  push Not at hno
  have hcell : ∀ i : ι,(∑ q ∈ labelFiber C label i,f q) ≤ eta*((labelFiber C label i).card : ℝ)+
      (if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0) := by
    intro i
    by_cases hi : ((labelFiber C label i).card : ℝ) < tau
    · rw [ite_eq_left hi]
      have hfi : (∑ q ∈ labelFiber C label i,f q) ≤ ((labelFiber C label i).card : ℝ) := by
        simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
          Finset.sum_le_sum (fun q hq => hf q (labelFiber_subset C label i hq))
      nlinarith [show (0 : ℝ) ≤ (labelFiber C label i).card from Nat.cast_nonneg _]
    · rw [ite_eq_right hi,add_zero]
      exact hno i (le_of_not_gt hi)
  have hcard : (∑ i : ι,((labelFiber C label i).card : ℝ)) = (C.card : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using sum_label_fibers C label (fun _ => (1 : ℝ))
  have hsmall : (∑ i : ι,if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0) =
      ((discardedPoints C label tau).card : ℝ) := by
    have hh := sum_small_fibers C label tau (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,smallLabels,Finset.sum_filter] using hh
  have hsum : (∑ q ∈ C,f q) ≤ eta*(C.card : ℝ)+((discardedPoints C label tau).card : ℝ) := by
    calc
      _ = ∑ i : ι,∑ q ∈ labelFiber C label i,f q := (sum_label_fibers C label f).symm
      _ ≤ ∑ i : ι,(eta*((labelFiber C label i).card : ℝ)+
          (if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hcard,hsmall]
  have hCp : (0 : ℝ) < C.card := by exact_mod_cast hC
  have hstrict := mul_lt_mul_of_pos_right hgap hCp
  nlinarith

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RefinementPrimeCongruences
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
namespace ErdosInverseRefinement
open ErdosInverseSampling ErdosInverseSampleCost ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem sampleModulus_pos (U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hU : ∀ u ∈ U,0 < u) : 0 < sampleModulus U h s :=
  Finset.prod_pos (fun i _ => hU _ (s i).property)

theorem sampleModulus_upper (U : Finset ℕ) (h : ℕ) (s : Sample U h) (T : ℝ)
    (hU : ∀ u ∈ U,(u : ℝ) ≤ T) : (sampleModulus U h s : ℝ) ≤ T^h := by
  unfold sampleModulus
  rw [Nat.cast_prod]
  have hh := Finset.prod_le_prod (s := Finset.univ) (fun i _ => Nat.cast_nonneg (s i).val)
    (fun i _ => hU _ (s i).property)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh

theorem source_sample_modulus_square (K eps : ℝ) (h : ℕ) (hK : 0 ≤ K) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,0 ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
      ∀ s : Sample (primeBin U theta) h,
        ((sampleModulus (primeBin U theta) h s : ℝ))^2 ≤ (sourceZ z)^eps := by
  let A : ℝ := (2*(h : ℝ))*(Real.log 2+K)
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  filter_upwards [sourceW_log_bounds,(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    exp_loglog_sq_le_sourceZ A eps hA heps] with z hz hs hExp
  intro U theta hU0 hUtop htheta htheta1 s
  have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  have hUL : U ≤ (Real.log z)^K := hUtop.trans (Real.rpow_le_rpow hWpos.le hz.2.2.2 hK)
  have hcap : ∀ u ∈ primeBin U theta,(u : ℝ) ≤ 2*U := by
    intro u hu
    have hh := ((mem_primeBin hU0 htheta u).mp hu).2.2
    nlinarith
  have hM := sampleModulus_upper (primeBin U theta) h s (2*U) hcap
  have hML : (sampleModulus (primeBin U theta) h s : ℝ) ≤ (2*(Real.log z)^K)^h :=
    hM.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hUL (by norm_num)) h)
  have hLL1 : 1 ≤ Real.log (Real.log z) := hs
  have hLL2 : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hsq1 : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hlogs : Real.log 2+K*Real.log (Real.log z) ≤ (Real.log 2+K)*(Real.log (Real.log z))^2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq1 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    have h2 := mul_le_mul_of_nonneg_left hLL2 hK
    nlinarith
  calc
    _ ≤ ((2*(Real.log z)^K)^h)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hML 2
    _ = Real.exp ((2*(h : ℝ))*(Real.log 2+K*Real.log (Real.log z))) := by
      rw [← pow_mul,← Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.rpow_pos_of_pos hz.2.1 K))]
      rw [← Real.exp_nat_mul]
      congr 1
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hz.2.1 K).ne',Real.log_rpow hz.2.1]
      push_cast
      ring
    _ ≤ Real.exp (A*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ 2*(h : ℝ) by positivity)
      dsimp [A]
      nlinarith
    _ ≤ _ := hExp

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceRefinedCell
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
namespace ErdosInverseRefinement
open ErdosInverseCells ErdosInverseSampling ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_refined_cell (K gamma : ℝ) (h : ℕ) (hK : 0 ≤ K) (hg : 0 < gamma) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,0 ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
      ∀ (s : Sample (primeBin U theta) h) (P C : Finset ℕ) (a : ℕ → ℕ)
        (witness : (ℕ × ℕ) → ℕ → Prop) (S : ℝ),
        0 < P.card → 0 < S → S/sourceZ z ≤ (C.card : ℝ) →
        gamma/2 ≤ selectedFraction (P.product C) (primeBin U theta) witness h s →
        ∃ i : RefinementLabel (sampleModulus (primeBin U theta) h s),
          S/(sourceZ z)^3 ≤ ((refinementCell C a (sampleModulus (primeBin U theta) h s) i).card : ℝ) ∧
          (refinementCell C a (sampleModulus (primeBin U theta) h s) i).Nonempty ∧
          (gamma/4)*((refinementCell C a (sampleModulus (primeBin U theta) h s) i).card : ℝ) <
            ∑ q ∈ refinementCell C a (sampleModulus (primeBin U theta) h s) i,
              rowReward P (primeBin U theta) witness h s q := by
  filter_upwards [source_sample_modulus_square K 1 h hK zero_lt_one,
    sourceZ_tendsto_atTop.eventually_ge_atTop (8/gamma)] with z hmod hZlarge
  intro U theta hU0 hUtop htheta htheta1 s P C a witness S hP hS hC hreward
  let W := sampleModulus (primeBin U theta) h s
  have hWpos : 0 < W := sampleModulus_pos _ h s
    (fun u hu => ((mem_primeBin hU0 htheta u).mp hu).1.pos)
  let : NeZero W := ⟨hWpos.ne'⟩
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hCpos : 0 < C.card := by exact_mod_cast (div_pos hS hZ).trans_le hC
  have hInv : 1/sourceZ z ≤ gamma/8 := by
    apply (div_le_iff₀ hZ).mpr
    have hh := (div_le_iff₀ hg).mp hZlarge
    nlinarith
  have hWsq : (W : ℝ)^2 ≤ sourceZ z := by
    simpa only [Real.rpow_one] using hmod U theta hU0 hUtop htheta htheta1 s
  have hDiscard := refined_discard_bound C a W S (sourceZ z) gamma hS.le hZ hC hWsq hInv
  have hMass : (gamma/2)*(C.card : ℝ) ≤ ∑ q ∈ C,rowReward P (primeBin U theta) witness h s q := by
    rw [rowReward_sum P C (primeBin U theta) witness h s hP hCpos]
    exact mul_le_mul_of_nonneg_right hreward (Nat.cast_nonneg _)
  obtain ⟨i,hlarge,hdense⟩ := dense_fiber_after_count_discard C (refinementLabel a W) (S/(sourceZ z)^3)
    (gamma/2) (gamma/4) (gamma/8) hCpos (by positivity) (by linarith)
    (rowReward P (primeBin U theta) witness h s)
    (fun q _ => (rowReward_bounds P (primeBin U theta) witness h s q hP).2) hMass hDiscard
  have hnR : (0 : ℝ) < (refinementCell C a W i).card :=
    (div_pos hS (pow_pos hZ 3)).trans_le hlarge
  have hn : 0 < (refinementCell C a W i).card := by exact_mod_cast hnR
  exact ⟨i,hlarge,Finset.card_pos.mp hn,hdense⟩

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRichPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost ErdosInverseHits ErdosInverseStructured
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem selectedRow_subset_nonstructured (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P U : Finset ℕ) (h : ℕ) (hh : 0 < h) (s : Sample U h)
    (T : ℕ → Finset ℤ) (q : ℕ) (hP : ∀ p ∈ P,p.Prime) (hqp : ∀ p ∈ P,q.Coprime p)
    (htest : ∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q ⊆
      nonstructuredPrimes P (fun p => (a p : ℤ)) T S R Z cp (cofactorPoint a q) := by
  intro p hp
  have hm := Finset.mem_filter.mp hp
  let : NeZero p := ⟨(hP p hm.1).ne_zero⟩
  have hn := (hm.2 ⟨0,hh⟩).1
  apply Finset.mem_filter.mpr
  refine ⟨hm.1,?_⟩
  refine ⟨parentSlope_incidence a T p q (hqp p hm.1) (htest p hm.1 (hqp p hm.1) hp),?_⟩
  simpa only [cofactorPoint,Int.toNat_natCast] using hn

theorem rich_points_incidence (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp gamma : ℝ) (D P U : Finset ℕ) (h : ℕ) (hh : 0 < h) (s : Sample U h)
    (T : ℕ → Finset ℤ) (hP : ∀ p ∈ P,p.Prime) (hPpos : 0 < P.card)
    (hqp : ∀ q ∈ D,∀ p ∈ P,q.Coprime p)
    (htest : ∀ q ∈ D,∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    ∀ v ∈ cofactorPoints (richCofactors D P U (actualWitness Y small a delta V0 P S R Z cp) h s gamma) a,
      (gamma/8)*(P.card : ℝ) ≤
        ((nonstructuredPrimes P (fun p => (a p : ℤ)) T S R Z cp v).card : ℝ) := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  have hqD := richCofactors_subset D P U _ h s gamma hq
  calc
    _ ≤ ((selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q).card : ℝ) :=
      richCofactor_row_card D P U _ h s gamma hPpos q hq
    _ ≤ _ := by
      exact_mod_cast Finset.card_le_card (selectedRow_subset_nonstructured Y small a delta V0 S R Z cp
        P U h hh s T q hP (hqp q hqD) (htest q hqD))

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseEuler ErdosInverseHits ErdosInverseStructured ErdosInverseTail
  ErdosInverseBoxHeight ErdosInversePrimeBin ErdosConvexGraph

theorem source_rich_points (aStar delta K gamma : ℝ) (h : ℕ)
    (ha : 0 < aStar) (hd : 0 < delta) (hK : 0 ≤ K) (hg : 0 < gamma) (hh : 0 < h) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ (P C : Finset ℕ) (a : ℕ → ℕ) (U theta Qplus S R cp : ℝ)
        (qInitial : ℕ) (bInitial : ℤ),
        0 < R → 0 < S → sourceW z ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
        0 < P.card → (∀ p ∈ P,p.Prime) →
        (∀ p ∈ P,∀ u ∈ primeBin U theta,p.Coprime u) →
        (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
        (∀ q ∈ C,∀ p ∈ P,q.Coprime p) →
        (∀ q ∈ C,∀ u ∈ primeBin U theta,q.Coprime u) →
        (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
        (∀ q ∈ C,∀ p ∈ P,∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ q ∈ C,∀ p ∈ P,∀ u ∈ primeBin U theta,
          ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t) →
        (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (qInitial : ℤ) ∧
          Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) bInitial) →
        S/sourceZ z ≤ (C.card : ℝ) →
        ∀ s : Sample (primeBin U theta) h,
          gamma/2 ≤ selectedFraction (P.product C) (primeBin U theta)
            (actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
              (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp) h s →
          actualCost (sourceY z) (sourceW z) Qplus R qInitial bInitial a (delta/4)
            P (primeBin U theta) h s ≤ 1/(Real.log z)^6 →
          ∃ (T : ℕ → Finset ℤ) (D : Finset ℕ),D ⊆ C ∧
            (∀ v ∈ cofactorPoints D a,InSquare S v) ∧
            Set.InjOn Prod.fst (cofactorPoints D a : Set (ℤ × ℤ)) ∧
            S/(sourceZ z)^4 ≤ ((cofactorPoints D a).card : ℝ) ∧
            (∀ v ∈ cofactorPoints D a,∀ ell ∈ v.1.toNat.primeFactors,
              (v.2 : ZMod ell) = (a ell : ZMod ell)) ∧
            (∀ v ∈ cofactorPoints D a,(gamma/8)*(P.card : ℝ) ≤
              ((nonstructuredPrimes P (fun p => (a p : ℤ)) T S R (sourceZ z) cp v).card : ℝ)) ∧
            (∑ p ∈ P,((T p).card : ℝ)) ≤ (P.card : ℝ)*R/(Real.log z)^6 := by
  classical
  obtain ⟨xi0,hxi0,hxi01,hparent⟩ := source_parentSlope_mem_jb247 aStar delta ha hd
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hparent xi hxi hxib,source_refined_cell K gamma h hK hg,
    sourceZ_tendsto_atTop.eventually_ge_atTop (8/gamma),sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hparentZ hrefine hZlarge hW
  intro P C a U theta Qplus S R cp qInitial bInitial hR hS hWU hUtop htheta htheta1 hPpos hP
    hpU hCsq hCP hCU hCQ hlog hsmall hcong hCsize s hreward hcost
  have hW0 : 0 ≤ sourceW z := by linarith
  have hU0 : 0 ≤ U := hW0.trans hWU
  let Uset := primeBin U theta
  have hUprime : ∀ u ∈ Uset,u.Prime := fun u hu => ((mem_primeBin hU0 htheta u).mp hu).1
  have huLarge : ∀ u ∈ Uset,sourceW z < (u : ℝ) := by
    intro u hu
    exact hWU.trans_lt ((mem_primeBin hU0 htheta u).mp hu).2.1
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
  obtain ⟨j,hjSize,hjNonempty,hjReward⟩ := hrefine U theta hU0 hUtop htheta htheta1 s P C a
    witness S hPpos hS hCsize hreward
  let C' := refinementCell C a (sampleModulus Uset h s) j
  have hC'C : C' ⊆ C := fun q hq => (mem_refinementCell C a _ j q).mp hq |>.1
  obtain ⟨qRef,hqRef⟩ := hjNonempty
  have hRefU : ∀ u ∈ Uset,qRef.Coprime u := hCU qRef (hC'C hqRef)
  let T := pointSlopes (sourceY z) (sourceW z) Qplus qInitial bInitial a (delta/4)
    P Uset h s hpU qRef (cofactorHit qRef a) hRefU
  let D := richCofactors C' P Uset witness h s gamma
  have hDC' : D ⊆ C' := richCofactors_subset C' P Uset witness h s gamma
  have hDC : D ⊆ C := hDC'.trans hC'C
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hInv : 1/sourceZ z ≤ gamma/8 := by
    apply (div_le_iff₀ hZ).mpr
    have hmul := (div_le_iff₀ hg).mp hZlarge
    nlinarith
  have htests : ∀ q ∈ C',∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P Uset witness h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p := by
    intro q hq p hp instP hcop hselected
    have hqC := hC'C hq
    have hselected' := Finset.mem_filter.mp hselected
    exact hparentZ P Uset C a h s hUprime hpU qRef hRefU j q p qInitial bInitial Qplus
      (hP p hp) hp hcop (hCsq q hqC).1 (hCU q hqC) hq hqRef
      (hCQ q hqC).1 (hCQ q hqC).2 (hlog q hqC p hp) (hsmall q hqC p hp)
      (hcong q hqC).1 (hcong q hqC).2 (fun i => (hselected'.2 i).2)
  refine ⟨T,D,hDC,cofactorPoints_square D a S (fun q hq => hCsq q (hDC hq)),
    cofactorPoints_x_injective D a,?_,cofactorPoints_prime_hits D a (fun q hq => (hCsq q (hDC hq)).1),?_,?_⟩
  · exact rich_points_source_size C' P Uset a witness h s gamma S (sourceZ z) hg hS.le hZ hPpos
      hjSize hInv hjReward.le
  · exact rich_points_incidence (sourceY z) _ a delta _ S R (sourceZ z) cp gamma C' P Uset h hh s T
      hP hPpos (fun q hq => hCP q (hC'C hq)) htests
  · exact pointSlopes_thin (sourceY z) (sourceW z) Qplus R (Real.log z) qInitial bInitial a (delta/4)
      P Uset h s hW0 hR hPpos hUprime huLarge hpU hcost qRef (cofactorHit qRef a) hRefU

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimePartitionCounts
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem prime_sum_partition_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (f : ℕ → ℝ) (hf : ∀ p ∈ P,0 ≤ f p) :
    (∑ p ∈ P,f p) ≤ (∑ p ∈ unalignedPrimes P a r,f p)+(∑ p ∈ ignoredPrimes P l.denominator,f p)+
      ∑ p ∈ P.filter (aligns a r.rational),f p := by
  calc
    _ ≤ ∑ p ∈ P,((if ¬p ∣ l.denominator ∧ ¬aligns a r.rational p then f p else 0)+
        (if p ∣ l.denominator then f p else 0)+(if aligns a r.rational p then f p else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hd : p ∣ l.denominator <;> by_cases ha : aligns a r.rational p <;>
        simp [hd,ha]
      linarith [hf p hp]
    _ = _ := by simp only [unalignedPrimes,ignoredPrimes,Finset.sum_filter,Finset.sum_add_distrib]

theorem many_aligners_of_richness {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (c eps : ℝ) (hN : 0 < X.card)
    (hrich : c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ))
    (hbad : (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
      eps*(P.card : ℝ)*(X.card : ℝ)) :
    (c-eps)*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ) := by
  have hp := prime_sum_partition_le r P a
    (fun p => ((incidentPoints X (a p) p (T p)).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  have ha := total_incidence_le_product (P.filter (aligns a r.rational)) X a T
  have hNp : (0 : ℝ) < X.card := by exact_mod_cast hN
  have hh : ((c-eps)*(P.card : ℝ))*(X.card : ℝ) ≤
      ((P.filter (aligns a r.rational)).card : ℝ)*(X.card : ℝ) := by linarith
  exact le_of_mul_le_mul_right hh hNp

theorem intercept_mem_fixed_list {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hnum : |(l.intercept : ℝ)| ≤ S*R*Z^10)
    (halign : cp*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ)) :
    r.rational ∈ sourceRationalList P a S R Z cp := by
  have hh := r.height_transfer (R*Z^10) (S*R*Z^10) hden hnum
  apply (mem_sourceRationalList P a hS hR r.rational).mpr
  refine ⟨?_,hh.1,halign⟩
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hh.2

end ErdosInverseStructured

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRichSetContradiction
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem nonstructuredPoints_eq_empty_of_aligned {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp) (hden : (l.denominator : ℝ) ≤ R*Z^10)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell))
    (p : ℕ) (halign : aligns a r.rational p) : nonstructuredPoints P X a T S R Z cp p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvX,_hslope,hnon⟩ := Finset.mem_filter.mp hv
  exact hnon (structured_of_line_alignment r P a S R Z cp p v.1.toNat v.2 hlist hden
    (contains_nat_abscissa l v (hbox v hvX).1.1 (hline v hvX)) (hclass v hvX) halign)

theorem nonstructured_total_le_bad {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp) (hden : (l.denominator : ℝ) ≤ R*Z^10)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell)) :
    (∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) ≤
      (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) := by
  have hpart := prime_sum_partition_le r P a
    (fun p => ((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  have hzero : (∑ p ∈ P.filter (aligns a r.rational),
      ((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [nonstructuredPoints_eq_empty_of_aligned r P X a T S R Z cp hlist hden hline hbox hclass p
      (Finset.mem_filter.mp hp).2,Finset.card_empty,Nat.cast_zero]
  rw [hzero,add_zero] at hpart
  apply hpart.trans
  apply add_le_add <;> apply Finset.sum_le_sum
  all_goals
    intro p hp
    exact Nat.cast_le.mpr (Finset.card_le_card (nonstructuredPoints_subset_incident P X a T S R Z cp p))

end ErdosInverseStructured

end

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph

theorem no_rich_nonstructured_line {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z c : ℝ)
    (hc : 0 < c) (hP : 0 < P.card) (hX : 0 < X.card) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell))
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hnum : |(l.intercept : ℝ)| ≤ S*R*Z^10)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z (c/4) v).card : ℝ))
    (hbad : (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
      (c/2)*(P.card : ℝ)*(X.card : ℝ)) : False := by
  classical
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX
  have htotal := all_incidence_lower_of_nonstructured_richness P X a T S R Z (c/4) c hrich
  have halign := many_aligners_of_richness r P X a T c (c/2) hX htotal hbad
  have hcp : (c/4)*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ) := by
    have hfrac : c/4 ≤ c-c/2 := by linarith
    exact (mul_le_mul_of_nonneg_right hfrac hPpos.le).trans halign
  have hlist := intercept_mem_fixed_list r P a S R Z (c/4) hS hR hden hnum hcp
  have hlow := nonstructured_total_lower P X a T S R Z (c/4) c hrich
  have hup := (nonstructured_total_le_bad r P X a T S R Z (c/4) hlist hden hline hbox hclass).trans hbad
  have hpos : 0 < c*(P.card : ℝ)*(X.card : ℝ) := mul_pos (mul_pos hc hPpos) hXpos
  linarith

end ErdosInverseStructured

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosSourcePolynomial ErdosSourceLineBudget ErdosConvexGraph

theorem uniform_no_rich_nonstructured_set (C Cparent eta alpha c : ℝ)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ),
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X,InSquare S v) →
          Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S/(sourceZ z)^4 ≤ (X.card : ℝ) →
          (∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell)) →
          (∀ v ∈ X,c*((primeBin R xi).card : ℝ) ≤
            ((nonstructuredPrimes (primeBin R xi) a T S R (sourceZ z) (c/4) v).card : ℝ)) → False := by
  classical
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_many heta 1)
  filter_upwards [uniform_original_rich_line_jb247 C Cparent eta alpha c hC hCp heta halpha hc,
    uniform_actual_bad_incidence eta alpha (c/2) heta halpha (by positivity),
    uniform_extraction_budget Cparent hCp,uniform_source_square_scale C hC,source_Z_ge_two,
    (tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hRich hBad hBudget hScale hZ2 hzR
  refine ⟨hRich.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen a T hthin
    X hbox hinj hsize hclass hrich
  have hcounts := hR0 R (hzR.trans hRlo)
  have hR1 : 1 ≤ R := by linarith [hcounts.1]
  have hRpos : 0 < R := by linarith
  have hPpos : 0 < (primeBin R xi).card := by
    have hh := hcounts.2 xi hxi hxi1
    omega
  have hqS : q ≤ S := (one_le_div hq).mp hratio
  have hS0 : 0 ≤ S := hq.le.trans hqS
  have hZpos : 0 < sourceZ z := by linarith
  have hbudget := hBudget.2 p q R S (by linarith) hq hpR hRhi hqS hlen
  have hthin' : (∑ r : primeBin R xi,((T r.val).card : ℝ)) ≤
      ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 := by
    calc
      _ = ∑ p ∈ primeBin R xi,((T p).card : ℝ) :=
        Finset.sum_coe_sort (primeBin R xi) (fun p : ℕ => ((T p).card : ℝ))
      _ ≤ _ := hthin
  have hpolyRich : ∀ v ∈ X,RichPoint R xi c (fun r => T r.val) (fun r => a r.val) v :=
    fun v hv => nonstructured_richness_implies_polynomial_richness R xi c S (sourceZ z) (c/4) a T v (hrich v hv)
  obtain ⟨l,Y,hsub,hlarge,hline,hdN,haN,hbN⟩ := hRich.2 S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen
    (fun r => T r.val) (fun r => a r.val) hthin' X hbox hinj hsize hpolyRich
  have hYposR : (0 : ℝ) < Y.card := by linarith [hbudget.2.1]
  have hYpos : 0 < Y.card := by exact_mod_cast hYposR
  have hYbox : ∀ v ∈ Y,InSquare S v := fun v hv => hbox v (hsub hv)
  have hYinj : Set.InjOn Prod.fst (Y : Set (ℤ × ℤ)) := fun _ hv _ hw he => hinj (hsub hv) (hsub hw) he
  have hYclass : ∀ v ∈ Y,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell) :=
    fun v hv => hclass v (hsub hv)
  have hYrich : ∀ v ∈ Y,c*((primeBin R xi).card : ℝ) ≤
      ((nonstructuredPrimes (primeBin R xi) a T S R (sourceZ z) (c/4) v).card : ℝ) :=
    fun v hv => hrich v (hsub hv)
  have hYsize : z^((93 : ℝ)/100) ≤ (Y.card : ℝ) := hbudget.1.trans hlarge.le
  have hSupper := hScale.2.2 S R p q xi hp hq hpq hratio hinfl hR1 hRhi (heta.le.trans hxi) hxi1
  obtain ⟨hd6,ha6,hb6⟩ := source_line_heights l S R (sourceZ z) (Y.card : ℝ) hS0 hRpos hZpos hYposR hlarge hdN haN hbN
  obtain ⟨hd10,_ha10,hb10⟩ := source_line_height_slack l S R (sourceZ z) hS0 hRpos.le hZ2 hd6 ha6 hb6
  obtain ⟨r⟩ := exists_intercept_reduction l
  have hbad := hBad.2 R xi S hRlo hRhi hxi hxi1 a T l r Y hline hYbox hYinj hSupper hYsize hthin hd10
  exact no_rich_nonstructured_line r (primeBin R xi) Y a T S R (sourceZ z) c hc hPpos hYpos hS0 hRpos.le
    hline hYbox hYclass hd10 hb10 hYrich hbad

end ErdosInverseStructured

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

theorem parent_small_coprime_child (p q u : ℕ) (w : ℝ) (hu : u.Prime) (hwu : w < (u : ℝ))
    (hparent : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) :
    ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q*u).Coprime t := by
  intro t ht htw
  apply (hparent t ht htw).mul_left
  apply (Nat.coprime_primes hu ht).mpr
  intro he
  subst u
  linarith

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseEuler ErdosInverseStructured ErdosInverseBoxHeight ErdosInversePrimeBin

theorem source_no_dense_cell_jb247_oai (Clen Cparent aStar K alpha delta beta : ℝ) (h : ℕ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ R thetaP U thetaU Qplus S : ℝ,
        ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
        z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → sourceW z ≤ U → U ≤ (sourceW z)^K →
        xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
        q0 ∈ C → 0 < q0 →
        S/(q0 : ℝ) ≤ (1+thetaP)^(Clen*Real.log (sourceB z)) →
        (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
        (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
        (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,p.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,q.Coprime p) →
        (∀ q ∈ C,∀ u ∈ primeBin U thetaU,q.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime →
          (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ p ∈ primeBin R thetaP,
          Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q0)) ≤ Cparent) →
        (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) ∧
          Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) b0) →
        S/sourceZ z ≤ (C.card : ℝ) →
        let P := primeBin R thetaP
        let Uset := primeBin U thetaU
        let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
        beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤
          ((witnessPairs (P.product C) Uset witness).card : ℝ) → False := by
  have hhpos : 0 < h := by
    by_contra hn
    have hz : h = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_div] at hh
    linarith
  let gamma := sampleGamma beta h
  have hg : 0 < gamma := sampleGamma_pos beta h hb
  obtain ⟨xi0,hxi0,hxi01,hRich⟩ := source_rich_points aStar delta K gamma h ha hd hK hg hhpos
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 : xi ≤ 1 := hxib.trans hxi01
  filter_upwards [source_good_sample_jb247 aStar K alpha xi delta beta h ha ha1 hK halpha hxi hxi1 hd hb hb1 hh,
    hRich xi hxi hxib,
    uniform_no_rich_nonstructured_set Clen Cparent (xi/4) alpha (gamma/8)
      hClen hCparent (by positivity) halpha (by positivity),
    sourceW_tendsto_atTop.eventually_ge_atTop 2] with z hgood hrich hno hW
  intro R thetaP U thetaU Qplus S C q0 b0 a hRlo hRhi hWU hUtop hPlow hPhigh hUlow hUhigh
    hq0C hq0 hinfl hCsq hCQ hpU hCP hCU hsmall hlog hparentlog hcong hCsize
  dsimp only
  intro hdense
  let P := primeBin R thetaP
  let Uset := primeBin U thetaU
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (gamma/32)
  obtain ⟨s,hPpos,hUpos,_,hreward,hcost⟩ := hgood.2 R thetaP U thetaU Qplus S C q0 b0 a
    hRlo hWU hUtop hPlow hPhigh hUlow hUhigh hq0C hq0 (hCQ q0 hq0C).1 (hCQ q0 hq0C).2
    (hsmall q0 hq0C) (hlog q0 hq0C) hdense
  have hzpos : 0 < z := by linarith [hgood.1]
  have hR : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hRlo
  have hU : 0 ≤ U := by linarith
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPprime : ∀ p ∈ P,p.Prime := fun p hp => ((mem_primeBin hR.le hthetaP p).mp hp).1
  have hUprime : ∀ u ∈ Uset,u.Prime := fun u hu => ((mem_primeBin hU hthetaU u).mp hu).1
  have huLarge : ∀ u ∈ Uset,sourceW z < (u : ℝ) :=
    fun u hu => hWU.trans_lt ((mem_primeBin hU hthetaU u).mp hu).2.1
  have hS : 0 < S := (show (0 : ℝ) < q0 by exact_mod_cast hq0).trans_le (hCsq q0 hq0C).2
  have hsmallChild : ∀ q ∈ C,∀ p ∈ P,∀ u ∈ Uset,∀ t : ℕ,t.Prime →
      (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t := by
    intro q hq p hp u hu
    exact parent_small_coprime_child p q u (sourceW z) (hUprime u hu) (huLarge u hu) (hsmall q hq p hp)
  obtain ⟨T,D,hDC,hbox,hinj,hsize,hclass,hinc,hthin⟩ := hrich P C a U thetaU Qplus S R (gamma/32)
    q0 b0 hR hS hWU hUtop hthetaU (hUhigh.trans hxi1) hPpos hPprime hpU hCsq hCP hCU hCQ
    hlog hsmallChild hcong hCsize s hreward hcost
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hPpos
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hUpos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPprime p hp).one_lt.le
  have hq0R : (0 : ℝ) < q0 := by exact_mod_cast hq0
  have hpq := parent_product_le_of_child_log (sourceY z) p q0 u (sourceW z) aStar
    (hPprime p hp).pos hq0 (hUprime u hu).one_lt.le (by linarith) ha (hlog q0 hq0C p hp u hu)
  have hratio : 1 ≤ S/(q0 : ℝ) := (one_le_div hq0R).mpr (hCsq q0 hq0C).2
  have hpR : (p : ℝ) ≤ 2*R := by
    have hh := ((mem_primeBin hR.le hthetaP p).mp hp).2.2
    have ht1 := hPhigh.trans hxi1
    nlinarith
  apply hno.2 S R (p : ℝ) (q0 : ℝ) thetaP hp1 hq0R hpq hratio hinfl
    hRlo hRhi hPlow (hPhigh.trans hxi1) hpR (hparentlog p hp)
    (fun p => (a p : ℤ)) T hthin (cofactorPoints D a) hbox hinj hsize
  · simpa only [Int.cast_natCast] using hclass
  · simpa only [div_div,show (8 : ℝ)*4 = 32 by norm_num] using hinc

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247_oai := @OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247_oai
