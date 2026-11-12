-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:11.365459+00:00
-- url     : https://prove2.me/submissions/b73d157c-4af1-411e-bdcd-3b4acc9d1ad1

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
import Theorems.Thm_OAI_Erdos970_ErdosInverseBoxApplication_actual_source_inverse_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem admitted_append (w r : ℝ) (i : Side) (ps qs : List ℕ) :
    admitted w i r (ps++qs) ↔ admitted w i r ps ∧ admitted w (endSide i ps) (primeFinalGap w r ps) qs := by
  induction ps generalizing i r with
  | nil => simp only [List.nil_append,admitted,primeFinalGap,endSide,true_and]
  | cons p ps ih =>
    simp only [List.cons_append,admitted,endSide,primeFinalGap,ih,and_assoc]

end NumberTheoryLean.ReferenceAdmission


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

end NumberTheoryLean.PrimeBinMembership

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



namespace NumberTheoryLean.IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open PrimeBinRepresentatives SourceStopPredicate
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem isolated_bin_search {w top xi B alpha beta : ℝ} {b : Fin (binCount w top xi)}
    (hb : isolatedBin w top xi B alpha beta b) (hscale : w^((1/4:ℝ)) ≤ alpha*B) :
    ActualSourceTags.searchBin w (lower w top xi b) := hscale.trans hb.1
end NumberTheoryLean.IsolatedBinGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceNodeCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open RegeneratingInverseBands ArrivalKernelGeometry SourceLowRemoval
open InvariantInverseWeights DerivativeWeights

theorem node_gap_eq {B : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : start.cutoff=B) : start.gap=B*start.ratio := by
  have he : start.cutoff=start.gap/start.ratio := hcons
  rw [hcut] at he
  exact ((eq_div_iff (valid_pos hs).ne').mp he).symm

end NumberTheoryLean.SourceNodeCoordinates

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

end ErdosInverseBoxHeight

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

theorem tripleWeight_nonneg (x : (ℕ × ℕ) × ℕ) : 0 ≤ tripleWeight x := by unfold tripleWeight;positivity

theorem triple_weight_sum (P Q U : Finset ℕ) :
    (∑ x ∈ tripleSpace P Q U,tripleWeight x) = harmonicMass P*harmonicMass Q*harmonicMass U := by
  simp only [tripleSpace,Finset.sum_product,tripleWeight,harmonicMass,mul_assoc,← Finset.mul_sum,← Finset.sum_mul]

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

end ErdosCofactorChoices

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

theorem actual_exception_weight (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) :
    (∑ t ∈ actualInverseException Y small a delta V0 S R Z cp P Q U,tripleWeight t) =
      weightedWitness P Q U (actualWitness Y small a delta V0 P S R Z cp) := rfl

end ErdosInverseBoxApplication

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeProductLogCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeProductLogCoordinates
open FinitePathGeometry PrimeHistories RepresentativeAdmission
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem log_nat_product (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    Real.log (ps.prod:ℝ)=(ps.map (fun p : ℕ => Real.log (p:ℝ))).sum := by
  rw [Nat.cast_list_prod]
  have hh := Real.log_list_prod (l := ps.map (fun p : ℕ => (p:ℝ))) (by
    intro x hx
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (hp p hp').ne')
  simpa only [List.map_map,Function.comp_def] using hh

theorem exponent_sum_log_product (w : ℝ) (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    (ps.map (primeExponent w)).sum=Real.log (ps.prod:ℝ)/Real.log w := by
  rw [log_nat_product ps hp]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,add_div,primeExponent]
    rw [ih (fun q hq => hp q (by simp [hq]))]

theorem terminal_gap_log_quotient {w a : ℝ} (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    (terminal w z ps).gap=Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log w-a+2 := by
  have hprodNat : 0 < ps.prod := List.prod_pos hp
  have hprod : 0 < (ps.prod:ℝ) := by exact_mod_cast hprodNat
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  rw [terminal_gap_sum,exponent_sum_log_product w ps hp,hroot,Real.log_div hYr.ne' hprod.ne']
  ring

end NumberTheoryLean.PrimeProductLogCoordinates


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



namespace NumberTheoryLean.SingletonBinSelection
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

theorem erase_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (i : Fin n) : eraseSelection f i ∈ selections P (eraseMultiplicity m i) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,eraseMultiplicity]
  · simpa only [eraseSelection,eraseMultiplicity,ite_eq_right hki] using (mem_selections P m f).mp hf k

theorem erased_coordinate_empty {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i)) : f i=∅ := by
  have hh := ((mem_selections P _ f).mp hf i).2
  simpa [eraseMultiplicity] using hh

theorem fill_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i))
    (p : ℕ) (hp : p ∈ P i) : fillSelection f i p ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [fillSelection,hmi,hp]
  · have hh := (mem_selections P _ f).mp hf k
    simpa [fillSelection,eraseMultiplicity,hki] using hh

theorem erase_fill {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    eraseSelection (fillSelection f i p) i=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem fill_erase {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i={p}) :
    fillSelection (eraseSelection f i) i p=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [fillSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem singleton_selection_recovery {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) :
    ∃ p ∈ P i,f i={p} ∧ fillSelection (eraseSelection f i) i p=f := by
  have hi := (mem_selections P m f).mp hf i
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (hi.2.trans hmi)
  exact ⟨p,hi.1 (by rw [hp]; simp),hp,fill_erase f i p hp⟩
end NumberTheoryLean.SingletonBinSelection



namespace NumberTheoryLean.PartitionedSelections
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

theorem restricted_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (S : Finset (Fin n)) :
    restrictSelection f S ∈ selections P (restrictMultiplicity m S) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : k∈S
  · simpa only [restrictSelection,restrictMultiplicity,ite_eq_left hk] using (mem_selections P m f).mp hf k
  · simp [restrictSelection,restrictMultiplicity,hk]

theorem restricted_empty {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (k : Fin n) (hk : k∉S) : f k=∅ := by
  have hh := ((mem_selections _ _ _).mp hf k).2
  simpa [restrictMultiplicity,hk] using hh

theorem joined_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) : joinSelection S f g ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : k∈S
  · have hh := (mem_selections _ _ _).mp hf k
    simpa [restrictMultiplicity,joinSelection,hk] using hh
  · have hh := (mem_selections _ _ _).mp hg k
    simpa [restrictMultiplicity,joinSelection,hk] using hh

theorem join_restrictions {n : ℕ} (f : Fin n → Finset ℕ) (S : Finset (Fin n)) :
    joinSelection S (restrictSelection f S) (restrictSelection f Sᶜ)=f := by
  funext k
  by_cases hk : k∈S <;> simp [joinSelection,restrictSelection,hk]

theorem restrict_join {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) :
    restrictSelection (joinSelection S f g) S=f ∧ restrictSelection (joinSelection S f g) Sᶜ=g := by
  constructor <;> funext k
  · by_cases hk : k∈S
    · simp [restrictSelection,joinSelection,hk]
    · simp only [restrictSelection,ite_eq_right hk]
      exact (restricted_empty P m S f hf k hk).symm
  · by_cases hk : k∈S
    · simp only [restrictSelection,Finset.mem_compl,not_true_eq_false,ite_false, if_false,hk]
      exact (restricted_empty P m Sᶜ g hg k (by simpa using hk)).symm
    · simp [restrictSelection,joinSelection,hk]
end NumberTheoryLean.PartitionedSelections



namespace NumberTheoryLean.SingletonBinProduct
open ErdosCofactorChoices SingletonBinSelection

attribute [local instance] Classical.propDecidable

theorem filled_product {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    selectionProduct (fillSelection f i p)=p*selectionProduct f := by
  have hp : ∀ k,(∏ q ∈ fillSelection f i p k,q)=(if k=i then p else 1)*(∏ q ∈ f k,q) := by
    intro k
    by_cases hki : k=i
    · subst k; simp [fillSelection,he]
    · simp [fillSelection,hki]
  unfold selectionProduct
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

theorem filled_reciprocal {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    (selectionProduct (fillSelection f i p):ℝ)⁻¹=(p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹ := by
  rw [filled_product f i p he,Nat.cast_mul,mul_inv_rev]
  ring

end NumberTheoryLean.SingletonBinProduct



namespace NumberTheoryLean.PartitionedSelectionSums
open ErdosCofactorChoices PartitionedSelections

attribute [local instance] Classical.propDecidable

theorem joined_product {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) :
    selectionProduct (joinSelection S f g)=selectionProduct f*selectionProduct g := by
  have hpoint : ∀ k,(∏ p ∈ joinSelection S f g k,p)=(∏ p ∈ f k,p)*(∏ p ∈ g k,p) := by
    intro k
    by_cases hk : k∈S
    · have he := restricted_empty P m Sᶜ g hg k (by simpa using hk)
      simp [joinSelection,hk,he]
    · have he := restricted_empty P m S f hf k hk
      simp [joinSelection,hk,he]
  unfold selectionProduct
  simp_rw [hpoint]
  exact Finset.prod_mul_distrib

theorem partitioned_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,G f)=
      ∑ f ∈ selections P (restrictMultiplicity m S),∑ g ∈ selections P (restrictMultiplicity m Sᶜ),G (joinSelection S f g) := by
  symm
  rw [← Finset.sum_product' (selections P (restrictMultiplicity m S))
    (selections P (restrictMultiplicity m Sᶜ)) (fun f g => G (joinSelection S f g))]
  apply Finset.sum_bij (fun x _ => joinSelection S x.1 x.2)
  · intro x hx
    exact joined_mem P m S x.1 x.2 (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
  · intro x hx y hy he
    have hx' := restrict_join P m S x.1 x.2 (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
    have hy' := restrict_join P m S y.1 y.2 (Finset.mem_product.mp hy).1 (Finset.mem_product.mp hy).2
    exact Prod.ext (hx'.1.symm.trans ((congrArg (fun f => restrictSelection f S) he).trans hy'.1))
      (hx'.2.symm.trans ((congrArg (fun f => restrictSelection f Sᶜ) he).trans hy'.2))
  · intro f hf
    exact ⟨(restrictSelection f S,restrictSelection f Sᶜ),
      Finset.mem_product.mpr ⟨restricted_mem P m f hf S,restricted_mem P m f hf Sᶜ⟩,join_restrictions f S⟩
  · intro x _hx
    rfl

theorem partitioned_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ f ∈ selections P (restrictMultiplicity m S),∑ g ∈ selections P (restrictMultiplicity m Sᶜ),
        ((selectionProduct f:ℝ)⁻¹*(selectionProduct g:ℝ)⁻¹)*G (joinSelection S f g) := by
  rw [partitioned_sum P m S]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  rw [joined_product P m S f g hf hg,Nat.cast_mul,mul_inv_rev]
  ring
end NumberTheoryLean.PartitionedSelectionSums



namespace NumberTheoryLean.SingletonBinSum
open ErdosCofactorChoices SingletonBinSelection SingletonBinProduct

attribute [local instance] Classical.propDecidable

theorem singleton_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),G (fillSelection f i p) := by
  symm
  rw [← Finset.sum_product' (P i) (selections P (eraseMultiplicity m i)) (fun p f => G (fillSelection f i p))]
  apply Finset.sum_bij (fun x _ => fillSelection x.2 i x.1)
  · intro x hx
    exact fill_selection_mem P m i hmi x.2 (Finset.mem_product.mp hx).2 x.1 (Finset.mem_product.mp hx).1
  · intro x hx y hy he
    have hpx : fillSelection x.2 i x.1 i={x.1} := by simp [fillSelection]
    have hpy : fillSelection y.2 i y.1 i={y.1} := by simp [fillSelection]
    have hp : x.1=y.1 := by
      have hh := congrFun he i
      rw [hpx,hpy] at hh
      exact Finset.singleton_injective hh
    have hf : x.2=y.2 := by
      have hh := congrArg (fun f => eraseSelection f i) he
      rwa [erase_fill x.2 i x.1 (erased_coordinate_empty P m i x.2 (Finset.mem_product.mp hx).2),
        erase_fill y.2 i y.1 (erased_coordinate_empty P m i y.2 (Finset.mem_product.mp hy).2)] at hh
    exact Prod.ext hp hf
  · intro f hf
    obtain ⟨p,hp,_hfp,he⟩ := singleton_selection_recovery P m i hmi f hf
    exact ⟨(p,eraseSelection f i),Finset.mem_product.mpr ⟨hp,erase_selection_mem P m f hf i⟩,he⟩
  · intro x _
    rfl

theorem singleton_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),
        ((p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G (fillSelection f i p) := by
  rw [singleton_sum P m i hmi]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro f hf
  rw [filled_reciprocal f i p (erased_coordinate_empty P m i f hf)]
end NumberTheoryLean.SingletonBinSum



namespace NumberTheoryLean.TwoSingletonBins
open ErdosCofactorChoices SingletonBinSelection SingletonBinProduct SingletonBinSum

attribute [local instance] Classical.propDecidable

theorem two_singleton_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : m i=1) (hj : m j=1) (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ p ∈ P i,∑ u ∈ P j,∑ f ∈ selections P (eraseTwo m i j),
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G (fillTwo f i j p u) := by
  rw [singleton_weighted_sum P m i hi]
  apply Finset.sum_congr rfl
  intro p _hp
  have hmj : eraseMultiplicity m i j=1 := by simp [eraseMultiplicity,Ne.symm hij,hj]
  have hh := singleton_weighted_sum P (eraseMultiplicity m i) j hmj
    (fun f => (p:ℝ)⁻¹*G (fillSelection f i p))
  calc
    _ = ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f:ℝ)⁻¹*((p:ℝ)⁻¹*G (fillSelection f i p)) := by
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by
      rw [hh]
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro f _hf
      dsimp only [fillTwo]
      ring
end NumberTheoryLean.TwoSingletonBins


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GeometricRegularWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.GeometricRegularWords
open FinitePathGeometry PrimeHistories ActualRegularBoxes RepeatedWordEvents NonisolatedWordOccurrence
open IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem geometric_isolated_prime {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z) :
    ∃ p ∈ ps,isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) := by
  have h := (Finset.mem_filter.mp hp).2.2
  simpa only [noIsolatedWord,not_forall,not_not,exists_prop] using h

end NumberTheoryLean.GeometricRegularWords


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FirstIsolatedPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FirstIsolatedPosition
open PrimeHistories GeometricRegularWords IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinLabels


theorem first_matching_position {α : Type*} (P : α → Prop) (ps : List α)
    (hex : ∃ p ∈ ps,P p) : ∃ pre p tail,ps=pre++p::tail ∧ P p ∧ ∀ q ∈ pre,¬P q := by
  classical
  induction ps with
  | nil => simp at hex
  | cons p ps ih =>
    by_cases hp : P p
    · exact ⟨[],p,ps,rfl,hp,by simp⟩
    · have ht : ∃ q ∈ ps,P q := by
        obtain ⟨q,hq,hP⟩ := hex
        rcases List.mem_cons.mp hq with rfl | hq
        · exact False.elim (hp hP)
        · exact ⟨q,hq,hP⟩
      obtain ⟨pre,q,tail,he,hq,hpre⟩ := ih ht
      exact ⟨p::pre,q,tail,by rw [List.cons_append,he],hq,by simpa using And.intro hp hpre⟩

theorem geometric_first_isolated {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z) :
    ∃ pre p tail,ps=pre++p::tail ∧
      isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) ∧
      ∀ q ∈ pre,¬isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi q) :=
  first_matching_position _ ps (geometric_isolated_prime hw htop hxi z ps hp)
end NumberTheoryLean.FirstIsolatedPosition


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_IsolatedSourceScales
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedSourceScales
open _root_.Filter PaperMissingPrimeWindow JacobsthalSourceScale
open scoped Topology

theorem source_isolated_search_scale {alpha : ℝ} (ha : 0 < alpha) :
    ∀ᶠ L : ℝ in atTop,(sourceW L)^((1/4:ℝ)) ≤ alpha*sourceB L := by
  have ht := (tendsto_rpow_atTop (show 0 < (3/4:ℝ) by norm_num)).comp sourceW_tendsto
  filter_upwards [sourceW_le_sourceB_eventually,sourceW_tendsto.eventually_gt_atTop 0,
    ht.eventually_ge_atTop (1/alpha)] with L hB hw hpow
  change 1/alpha ≤ (sourceW L)^((3/4:ℝ)) at hpow
  have hprod : (sourceW L)^((1/4:ℝ))*(sourceW L)^((3/4:ℝ))=sourceW L := by
    rw [← Real.rpow_add hw]
    norm_num
  have hlow := mul_le_mul_of_nonneg_left hpow (Real.rpow_pos_of_pos hw (1/4:ℝ)).le
  rw [hprod] at hlow
  have hmain : (sourceW L)^((1/4:ℝ)) ≤ alpha*sourceW L := by
    have hm := mul_le_mul_of_nonneg_left hlow ha.le
    field_simp [ha.ne'] at hm
    nlinarith
  exact hmain.trans (mul_le_mul_of_nonneg_left hB ha.le)
end NumberTheoryLean.IsolatedSourceScales


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



namespace NumberTheoryLean.BinCutSelections
open ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem above_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (j : Fin n) : aboveSelection f j ∈ selections P (aboveMultiplicity m j) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases h : j<k
  · simpa only [aboveSelection,aboveMultiplicity,ite_eq_left h] using (mem_selections P m f).mp hf k
  · simp [aboveSelection,aboveMultiplicity,h]

theorem below_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (j : Fin n) : belowSelection f j ∈ selections P (belowMultiplicity m j) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases h : k<j
  · simpa only [belowSelection,belowMultiplicity,ite_eq_left h] using (mem_selections P m f).mp hf k
  · simp [belowSelection,belowMultiplicity,h]

theorem above_word_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (p : ℕ) :
    p ∈ descendingWord (aboveSelection f j) ↔ p ∈ descendingWord f ∧ j<label (zero_lt_one.trans hw) htop hxi p := by
  rw [mem_descendingWord,mem_descendingWord]
  constructor
  · rintro ⟨k,hp⟩
    by_cases h : j<k
    · have hpf : p ∈ f k := by simpa only [aboveSelection,ite_eq_left h] using hp
      refine ⟨⟨k,hpf⟩,?_⟩
      rwa [selected_prime_label hw htop hxi m f hf k hpf]
    · simp [aboveSelection,h] at hp
  · rintro ⟨⟨k,hp⟩,hj⟩
    have h : j<k := by rwa [selected_prime_label hw htop hxi m f hf k hp] at hj
    exact ⟨k,by simpa only [aboveSelection,ite_eq_left h] using hp⟩

theorem below_word_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (p : ℕ) :
    p ∈ descendingWord (belowSelection f j) ↔ p ∈ descendingWord f ∧ label (zero_lt_one.trans hw) htop hxi p<j := by
  rw [mem_descendingWord,mem_descendingWord]
  constructor
  · rintro ⟨k,hp⟩
    by_cases h : k<j
    · have hpf : p ∈ f k := by simpa only [belowSelection,ite_eq_left h] using hp
      refine ⟨⟨k,hpf⟩,?_⟩
      rwa [selected_prime_label hw htop hxi m f hf k hpf]
    · simp [belowSelection,h] at hp
  · rintro ⟨⟨k,hp⟩,hj⟩
    have h : k<j := by rwa [selected_prime_label hw htop hxi m f hf k hp] at hj
    exact ⟨k,by simpa only [belowSelection,ite_eq_left h] using hp⟩
end NumberTheoryLean.BinCutSelections



namespace NumberTheoryLean.SourceLabelStrictOrder
open ErdosSubsetWord LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem prime_lt_of_label_lt {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top)
    (hl : label (zero_lt_one.trans hw) htop hxi p<label (zero_lt_one.trans hw) htop hxi q) : p<q := by
  by_contra! hn
  exact (not_le_of_gt hl) (global_label_mono hw htop hxi hp hq hn)
end NumberTheoryLean.SourceLabelStrictOrder



namespace NumberTheoryLean.AssembleAtBin
open ErdosCofactorChoices BinCutSelections SingletonBinSelection
attribute [local instance] Classical.propDecidable

theorem above_zero_outside {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (parent : Fin n → Finset ℕ) (j k : Fin n) (hf : parent ∈ selections P (aboveMultiplicity m j))
    (hk : ¬j<k) : parent k=∅ := by
  have hh := ((mem_selections _ _ _).mp hf k).2
  simpa only [aboveMultiplicity,ite_eq_right hk,Finset.card_eq_zero] using hh

theorem assembled_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ)
    (ha : anchor ∈ selections P m) (hf : parent ∈ selections P (aboveMultiplicity m j))
    (hj : m j=1) (hu : u ∈ P j) : assemble anchor parent j u ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : j<k
  · have hh := (mem_selections _ _ _).mp hf k
    simpa only [assemble,aboveMultiplicity,ite_eq_left hk] using hh
  · by_cases hkj : k=j
    · subst k; simp [assemble,hj,hu]
    · simpa only [assemble,ite_eq_right hk,ite_eq_right hkj] using (mem_selections _ _ _).mp ha k

theorem assembled_above {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ)
    (hf : parent ∈ selections P (aboveMultiplicity m j)) :
    aboveSelection (assemble anchor parent j u) j=parent := by
  funext k
  by_cases hk : j<k
  · simp [aboveSelection,assemble,hk]
  · simp only [aboveSelection,ite_eq_right hk]
    exact (above_zero_outside P m parent j k hf hk).symm

theorem assembled_edge {n : ℕ} (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) :
    assemble anchor parent j u j={u} := by simp [assemble]

end NumberTheoryLean.AssembleAtBin



namespace NumberTheoryLean.BinCutGapMovement
open FinitePathGeometry PrimeHistories ErdosCofactorChoices ErdosSubsetWord BinCutSelections
open SafeSubsetBoxGeometry RepresentativeAdmission SourceStopPredicate
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints LogarithmicBinMaps

theorem above_total_le {n : ℕ} (m : Fin n → ℕ) (j : Fin n) :
    (∑ k,aboveMultiplicity m j k) ≤ ∑ k,m k := by
  apply Finset.sum_le_sum
  intro k _
  unfold aboveMultiplicity
  split_ifs <;> omega

theorem above_word_length_le {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    (descendingWord (aboveSelection f j)).length ≤ ∑ k,m k := by
  rw [global_word_length hw htop hxi _ _ (above_selection_mem _ m f hf j)]
  exact above_total_le m j

theorem above_gap_movement {w top xi B C : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (m : Fin (binCount w top xi) → ℕ) (hlen : ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B)
    (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (hg : g ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) :
    |(terminal w z (descendingWord (aboveSelection f j))).gap-
      (terminal w z (descendingWord (aboveSelection g j))).gap| ≤ 2*C*xi := by
  have hfA := above_selection_mem _ m f hf j
  have hgA := above_selection_mem _ m g hg j
  have hlF : ((descendingWord (aboveSelection f j)).length:ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (above_word_length_le hw htop hxi m f hf j)).trans hlen
  have hlG : ((descendingWord (aboveSelection g j)).length:ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (above_word_length_le hw htop hxi m g hg j)).trans hlen
  have hF := source_prefix_movement hw htop hxi hC hcomp z _ (word_source_membership hw htop hxi _ _ hfA) hlF
  have hG := source_prefix_movement hw htop hxi hC hcomp z _ (word_source_membership hw htop hxi _ _ hgA) hlG
  have he := selection_representatives_eq hw htop hxi _ _ _ hfA hgA
  have hrep : representativeGap (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z.gap (descendingWord (aboveSelection f j))=
    representativeGap (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z.gap (descendingWord (aboveSelection g j)) := by
    unfold representativeGap
    rw [he]
  rw [hrep] at hF
  exact abs_le.mpr ⟨by linarith [hF.1,hG.2],by linarith [hF.2,hG.1]⟩
end NumberTheoryLean.BinCutGapMovement


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FullBoxPrefixLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualReferencePrefixes
open FinitePathGeometry PrimeHistories ReferenceAdmission StrongSourceFamilies StrongReferenceTransport
open PrimeBinMembership LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_prefix_mem (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (ps pre : List ℕ)
    (hp : ps ∈ referencePrefixes w P i r) (hpre : pre ∈ ps.inits) : pre ∈ referencePrefixes w P i r := by
  obtain ⟨tail,he⟩ := (List.mem_inits pre ps).mp hpre
  obtain ⟨hd,ha⟩ := Finset.mem_filter.mp hp
  obtain ⟨horder,hmem⟩ := mem_decreasingPrefixes.mp hd
  rw [← he] at horder ha
  apply Finset.mem_filter.mpr
  refine ⟨mem_decreasingPrefixes.mpr ⟨(List.pairwise_append.mp horder).1,?_⟩,
    ((admitted_append w r i pre tail).mp ha).1⟩
  intro p hp
  exact hmem p (by rw [← he]; exact List.mem_append_left _ hp)

theorem reference_prefix_gap_floor {w top : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (ps pre : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap) (hpre : pre ∈ ps.inits) :
    2 ≤ (terminal w z pre).gap :=
  (source_reference_transport hw htop z hs hz hg hclosed hcap pre (reference_prefix_mem w _ _ _ ps pre hp hpre)).2
end NumberTheoryLean.ActualReferencePrefixes



namespace NumberTheoryLean.SelectionWordSplit
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections SourceLabelStrictOrder
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem selected_word_split {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi))
    (u : ℕ) (hfu : f j={u}) :
    descendingWord f=descendingWord (aboveSelection f j)++u::descendingWord (belowSelection f j) := by
  have hu : u ∈ f j := by rw [hfu]; simp
  have hul := selected_prime_label hw htop hxi m f hf j hu
  have humem : u ∈ descendingWord f := (mem_descendingWord f u).mpr ⟨j,hu⟩
  have hsource := word_source_membership hw htop hxi m f hf
  have hsmaller : ∀ p ∈ descendingWord (belowSelection f j),p<u := by
    intro p hp
    have hh := (below_word_membership hw htop hxi m f hf j p).mp hp
    apply prime_lt_of_label_lt hw htop hxi (hsource p hh.1) (hsource u humem)
    rw [hul]
    exact hh.2
  have hgreater : ∀ p ∈ descendingWord (aboveSelection f j),u<p := by
    intro p hp
    have hh := (above_word_membership hw htop hxi m f hf j p).mp hp
    apply prime_lt_of_label_lt hw htop hxi (hsource u humem) (hsource p hh.1)
    rw [hul]
    exact hh.2
  have hright : (descendingWord (aboveSelection f j)++u::descendingWord (belowSelection f j)).Pairwise (· > ·) := by
    rw [List.pairwise_append,List.pairwise_cons]
    refine ⟨descendingWord_strict _,⟨hsmaller,descendingWord_strict _⟩,?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hgreater a ha
    · exact (hsmaller b hb).trans (hgreater a ha)
  apply (descendingWord_strict f).eq_of_mem_iff hright
  intro p
  constructor
  · intro hp
    obtain ⟨k,hpk⟩ := (mem_descendingWord f p).mp hp
    have hpl := selected_prime_label hw htop hxi m f hf k hpk
    rcases lt_trichotomy k j with hlt | rfl | hgt
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((below_word_membership hw htop hxi m f hf j p).mpr ⟨hp,by rwa [hpl]⟩))
    · have he : p=u := by simpa only [hfu,Finset.mem_singleton] using hpk
      subst p
      simp
    · exact List.mem_append_left _ ((above_word_membership hw htop hxi m f hf j p).mpr ⟨hp,by rwa [hpl]⟩)
  · intro hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ((above_word_membership hw htop hxi m f hf j p).mp hp).1
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact humem
      · exact ((below_word_membership hw htop hxi m f hf j p).mp hp).1
end NumberTheoryLean.SelectionWordSplit



namespace NumberTheoryLean.BinCutPrefixGeometry
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections SelectionWordSplit
open PrimeHistories PrimeProductLogCoordinates
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem above_word_is_prefix {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi))
    (u : ℕ) (hfu : f j={u}) :
    descendingWord (aboveSelection f j) ∈ (descendingWord f).inits ∧
      descendingWord (aboveSelection f j)++[u] ∈ (descendingWord f).inits := by
  have he := selected_word_split hw htop hxi m f hf j u hfu
  constructor
  · exact (List.mem_inits _ _).mpr ⟨u::descendingWord (belowSelection f j),he.symm⟩
  · apply (List.mem_inits _ _).mpr
    refine ⟨descendingWord (belowSelection f j),?_⟩
    simpa only [List.append_assoc,List.singleton_append] using he.symm

theorem above_word_product {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    (descendingWord (aboveSelection f j)).prod=selectionProduct (aboveSelection f j) := by
  apply descendingWord_product (globalBins w top xi)
    (fun i k hik => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i k hik)
  intro k
  exact ((mem_selections _ _ _).mp (above_selection_mem _ m f hf j) k).1
end NumberTheoryLean.BinCutPrefixGeometry



namespace NumberTheoryLean.FullBoxPrefixLower
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport StrongSourceFamilies
open ErdosCofactorChoices ErdosSubsetWord SafeSubsetBoxGeometry ActualReferencePrefixes BinCutSelections BinCutPrefixGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

theorem full_box_child_gap_floor {w top xi B C K : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) :
    2 ≤ (terminal w z (descendingWord (aboveSelection f j)++[u])).gap := by
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hprefix := (above_word_is_prefix hw htop hxi m f hf j u hu).2
  exact reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap _ _ hfull hprefix
end NumberTheoryLean.FullBoxPrefixLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OriginalCofactorSums
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.OriginalCofactorSums
open ErdosCofactorChoices TwoSingletonBins

attribute [local instance] Classical.propDecidable

theorem cofactor_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : ℕ → ℝ) :
    (∑ f ∈ selections P m,G (selectionProduct f))=∑ q ∈ cofactorChoices P m,G q := by
  symm
  rw [cofactorChoices,Finset.sum_image]
  exact fun f hf g hg he => selectionProduct_injOn P m hP hd hf hg he

end NumberTheoryLean.OriginalCofactorSums


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TwoPrimeObservableSum
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.TwoPrimeObservableSum
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins OriginalCofactorSums

attribute [local instance] Classical.propDecidable

theorem picked_fillTwo {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) (hij : i ≠ j) (p u : ℕ) :
    pickedPrime (fillTwo f i j p u) i=p ∧ pickedPrime (fillTwo f i j p u) j=u := by
  simp [pickedPrime,fillTwo,fillSelection,Ne.symm hij]

end NumberTheoryLean.TwoPrimeObservableSum


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoundedEdgeBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FullBoxLengthBounds
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections BinCutPrefixGeometry BinCutGapMovement
open SafeSubsetBoxGeometry FullBoxPrefixLower PrimeProductLogCoordinates
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition


theorem parent_length_gap {w top xi a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    parentLength w Y f j=(terminal w z (descendingWord (aboveSelection f j))).gap+a-2 := by
  have hsource := word_source_membership hw htop hxi _ _ (above_selection_mem _ m f hf j)
  have hg := terminal_gap_log_quotient Y hY z hroot (descendingWord (aboveSelection f j))
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos)
  rw [above_word_product hw htop hxi m f hf j] at hg
  unfold parentLength
  linarith

theorem child_length_gap {w top xi a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) :
    childLength w Y f j u=(terminal w z (descendingWord (aboveSelection f j)++[u])).gap+a-2 := by
  have hfull := word_source_membership hw htop hxi m f hf
  have hpre := (above_word_is_prefix hw htop hxi m f hf j u hu).2
  have hsub : descendingWord (aboveSelection f j)++[u] ⊆ descendingWord f := by
    obtain ⟨tail,he⟩ := (List.mem_inits _ _).mp hpre
    intro p hp
    rw [← he]
    exact List.mem_append_left _ hp
  have hg := terminal_gap_log_quotient Y hY z hroot (descendingWord (aboveSelection f j)++[u])
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hfull p (hsub hp))).1.pos)
  rw [List.prod_append,List.prod_singleton,above_word_product hw htop hxi m f hf j,Nat.cast_mul] at hg
  unfold childLength
  linarith

theorem parent_length_movement {w top xi B C a : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ C) (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (m : Fin (binCount w top xi) → ℕ) (hlen : ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B)
    (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (hg : g ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) : |parentLength w Y f j-parentLength w Y g j| ≤ 2*C*xi := by
  rw [parent_length_gap hw htop hxi Y hY z hroot m f hf j,parent_length_gap hw htop hxi Y hY z hroot m g hg j]
  convert above_gap_movement hw htop hxi hC hcomp z m hlen f g hf hg j using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem full_box_child_length_lower {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (j : Fin (binCount w top xi)) (u : ℕ) (hu : f j={u}) : a ≤ childLength w Y f j u := by
  rw [child_length_gap hw htop hxi Y hY z hroot m f hf j u hu]
  have hh := full_box_child_gap_floor hw htop hxi hC hcomp z hs hz hg hclosed hcap m ha f hf j u hu
  linarith
end NumberTheoryLean.FullBoxLengthBounds



namespace NumberTheoryLean.BoundedEdgeBins
open ErdosCofactorChoices ErdosSubsetWord FullBoxLengthBounds
open FinitePathGeometry PrimeHistories SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem bounded_edge_singleton {w top xi M X : ℝ} {Y : ℕ}
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) : m j=1 := by
  obtain ⟨f,hf,u,hfu,_⟩ := hj
  have hh := ((mem_selections _ _ _).mp hf j).2
  simpa [hfu] using hh.symm

theorem anchor_total_length {w top xi B C K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (z : Node) (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m) :
    ((∑ k,m k : ℕ):ℝ) ≤ C*Real.log B := by
  obtain ⟨g,hg,hlen,_⟩ := ha
  rwa [global_word_length hw htop hxi m g hg] at hlen
end NumberTheoryLean.BoundedEdgeBins


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CofactorAllChoiceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentCofactorChoices
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections AssembleAtBin SingletonBinSelection SingletonBinProduct
open BinCutPrefixGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem cofactor_slots_zero {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) :
    parentCofactorMultiplicity m i j i=0 ∧ parentCofactorMultiplicity m i j j=0 := by
  simp [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity]

theorem cofactor_total_le {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) :
    (∑ k,parentCofactorMultiplicity m i j k) ≤ ∑ k,m k := by
  apply Finset.sum_le_sum
  intro k _
  simp only [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity]
  split_ifs <;> omega

theorem complete_parent_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (anchor f : Fin n → Finset ℕ) (ha : anchor ∈ selections P m)
    (hf : f ∈ selections P (parentCofactorMultiplicity m i j)) (p u : ℕ) (hp : p ∈ P i) (hu : u ∈ P j) :
    completeParent anchor f i j p u ∈ selections P m := by
  have hmi : aboveMultiplicity m j i=1 := by simp [aboveMultiplicity,hji,hi]
  exact assembled_mem P m anchor _ j u ha (fill_selection_mem P _ i hmi f hf p hp) hj hu

theorem complete_parent_product {w top xi : ℝ} (_hw : 1 < w) (_htop : w < top) (_hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (anchor f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (parentCofactorMultiplicity m i j))
    (p u : ℕ) (hp : p ∈ globalBins w top xi i) :
    selectionProduct (aboveSelection (completeParent anchor f i j p u) j)=p*selectionProduct f := by
  have hmi : aboveMultiplicity m j i=1 := by simp [aboveMultiplicity,hji,hi]
  have hfill := fill_selection_mem (globalBins w top xi) _ i hmi f hf p hp
  rw [completeParent,assembled_above _ m anchor _ j u hfill]
  exact filled_product f i p (erased_coordinate_empty _ (aboveMultiplicity m j) i f hf)
end NumberTheoryLean.ParentCofactorChoices



namespace NumberTheoryLean.CofactorAllChoiceBounds
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections AssembleAtBin ParentCofactorChoices
open FullBoxLengthBounds BoundedEdgeBins SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem cofactor_all_choice_lengths {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (hj : boundedEdgeBin w top xi Y m M X j) :
    (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log w ≤ M+2*C*xi) ∧
    (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
        a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)*(u:ℝ)))/Real.log w) := by
  have hmj := bounded_edge_singleton m j hj
  obtain ⟨g,hgmem,u₀,hgju,hparent,_hx⟩ := hj
  have hu₀ : u₀ ∈ globalBins w top xi j := ((mem_selections _ _ _).mp hgmem j).1 (by rw [hgju]; simp)
  have hlen := anchor_total_length hw htop hxi z m ha
  have hall : ∀ f ∈ selections (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
      Real.log ((Y:ℝ)/((p:ℝ)*(selectionProduct f:ℝ)))/Real.log w ≤ M+2*C*xi ∧
      a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(selectionProduct f:ℝ)*(u:ℝ)))/Real.log w := by
    intro f hf p hp u hu
    let F := completeParent g f i j p u
    have hF : F ∈ selections (globalBins w top xi) m := complete_parent_mem _ m i j hji hi hmj g f hgmem hf p u hp hu
    have hFu : F j={u} := assembled_edge _ _ j u
    have hprod : selectionProduct (aboveSelection F j)=p*selectionProduct f := complete_parent_product hw htop hxi m i j hji hi g f hf p u hp
    have hmove := parent_length_movement hw htop hxi hC hcomp Y hY z hroot m hlen F g hF hgmem j
    have hupper : parentLength w Y F j ≤ M+2*C*xi := by linarith [(abs_le.mp hmove).2]
    have hlower := full_box_child_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m ha F hF j u hFu
    simpa only [parentLength,childLength,hprod,Nat.cast_mul] using And.intro hupper hlower
  constructor
  · intro q hq p hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
    exact (hall f hf p hp u₀ hu₀).1
  · intro q hq p hp u hu
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
    exact (hall f hf p hp u hu).2
end NumberTheoryLean.CofactorAllChoiceBounds


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualBoxFourSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentTailPartition
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins TwoPrimeObservableSum
open BinCutSelections ParentCofactorChoices PartitionedSelections

attribute [local instance] Classical.propDecidable

theorem residual_partition_multiplicity {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) (hji : j < i) :
    restrictMultiplicity (eraseTwo m i j) (aboveIndexSet j)=parentCofactorMultiplicity m i j ∧
    restrictMultiplicity (eraseTwo m i j) (aboveIndexSet j)ᶜ=belowMultiplicity m j := by
  constructor <;> funext k <;>
    simp only [restrictMultiplicity,eraseTwo,eraseMultiplicity,parentCofactorMultiplicity,
      aboveMultiplicity,belowMultiplicity,aboveIndexSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl] <;>
    split_ifs <;> omega

theorem filled_parent_tail {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (f g : Fin n → Finset ℕ)
    (hf : f ∈ selections P (parentCofactorMultiplicity m i j))
    (hg : g ∈ selections P (belowMultiplicity m j)) (p u : ℕ) :
    parentCofactorSelection (fillTwo (joinSelection (aboveIndexSet j) f g) i j p u) i j=f ∧
    belowSelection (fillTwo (joinSelection (aboveIndexSet j) f g) i j p u) j=g := by
  have hfmem := (mem_selections P _ f).mp hf
  have hgmem := (mem_selections P _ g).mp hg
  constructor <;> funext k
  · by_cases hki : k=i
    · subst k
      have he : f i=∅ := Finset.card_eq_zero.mp ((hfmem i).2.trans (cofactor_slots_zero m i j).1)
      simp [parentCofactorSelection,eraseSelection,he]
    · by_cases hjk : j<k
      · have hkj : k≠j := ne_of_gt hjk
        simp [parentCofactorSelection,eraseSelection,aboveSelection,fillTwo,fillSelection,
          joinSelection,aboveIndexSet,hki,hjk,hkj]
      · have he : f k=∅ := by
          have hh := (hfmem k).2
          simpa [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity,hki,hjk] using hh
        simp [parentCofactorSelection,eraseSelection,aboveSelection,hki,hjk,he]
  · by_cases hkj : k<j
    · have hki : k≠i := ne_of_lt (hkj.trans hji)
      have hkje : k≠j := ne_of_lt hkj
      simp [belowSelection,fillTwo,fillSelection,joinSelection,aboveIndexSet,hkj,hki,hkje,not_lt_of_ge hkj.le]
    · have he : g k=∅ := by
        have hh := (hgmem k).2
        simpa [belowMultiplicity,hkj] using hh
      simp [belowSelection,hkj,he]
end NumberTheoryLean.ParentTailPartition



namespace NumberTheoryLean.FourCoordinateBoxSum
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins TwoPrimeObservableSum OriginalCofactorSums
open BinCutSelections ParentCofactorChoices ParentTailPartition PartitionedSelections PartitionedSelectionSums

attribute [local instance] Classical.propDecidable

theorem four_selection_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (parentCofactorSelection f i j)) (selectionProduct (belowSelection f j)))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ f ∈ selections P (parentCofactorMultiplicity m i j),∑ g ∈ selections P (belowMultiplicity m j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(selectionProduct g:ℝ)⁻¹)*G p u (selectionProduct f) (selectionProduct g) := by
  have hij : i≠j := ne_of_gt hji
  rw [two_singleton_weighted_sum P m i j hij hi hj]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  let H : (Fin n → Finset ℕ) → ℝ := fun f =>
    G (pickedPrime (fillTwo f i j p u) i) (pickedPrime (fillTwo f i j p u) j)
      (selectionProduct (parentCofactorSelection (fillTwo f i j p u) i j))
      (selectionProduct (belowSelection (fillTwo f i j p u) j))
  change (∑ f ∈ selections P (eraseTwo m i j),((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*H f)=_
  calc
    _ = ∑ f ∈ selections P (eraseTwo m i j),(selectionProduct f:ℝ)⁻¹*((p:ℝ)⁻¹*(u:ℝ)⁻¹*H f) := by
      apply Finset.sum_congr rfl
      intro f _hf
      ring
    _ = _ := by
      rw [partitioned_weighted_sum P (eraseTwo m i j) (aboveIndexSet j)]
      have he := residual_partition_multiplicity m i j hji
      rw [he.1,he.2]
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro g hg
      have hpick := picked_fillTwo (joinSelection (aboveIndexSet j) f g) i j hij p u
      have hsplit := filled_parent_tail P m i j hji f g hf hg p u
      dsimp only [H]
      rw [hpick.1,hpick.2,hsplit.1,hsplit.2]
      ring

theorem four_coordinate_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (parentCofactorSelection f i j)) (selectionProduct (belowSelection f j)))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ q ∈ cofactorChoices P (parentCofactorMultiplicity m i j),∑ d ∈ cofactorChoices P (belowMultiplicity m j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u q d := by
  rw [four_selection_sum P m i j hji hi hj]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  calc
    _ = ∑ f ∈ selections P (parentCofactorMultiplicity m i j),∑ d ∈ cofactorChoices P (belowMultiplicity m j),
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u (selectionProduct f) d := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact cofactor_sum P (belowMultiplicity m j) hP hd (fun d =>
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u (selectionProduct f) d)
    _ = _ := cofactor_sum P (parentCofactorMultiplicity m i j) hP hd (fun q =>
      ∑ d ∈ cofactorChoices P (belowMultiplicity m j),((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p u q d)
end NumberTheoryLean.FourCoordinateBoxSum



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundedEdgeHighPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.BoundedEdgePrimeRange
open ErdosCofactorChoices ErdosSubsetWord BoundedEdgeBins
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem bounded_edge_lower_exponent {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) : leftExponent w (lower w top xi j) ≤ X := by
  obtain ⟨f,hf,u,hfu,_hm,hx⟩ := hj
  have hu : u ∈ globalBins w top xi j := ((mem_selections _ _ _).mp hf j).1 (by rw [hfu]; simp)
  have hh := bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) j.1)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hu
  exact hh.1.le.trans hx

theorem bounded_edge_prime_range {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) :
    w ≤ lower w top xi j ∧ lower w top xi j ≤ w^X := by
  refine ⟨(bin_source_bounds (zero_lt_one.trans hw) htop hxi j).1,?_⟩
  have hx := bounded_edge_lower_exponent hw htop hxi m j hj
  have hh : Real.log (lower w top xi j) ≤ X*Real.log w := (div_le_iff₀ (Real.log_pos hw)).mp hx
  apply (Real.log_le_log_iff (endpoint_pos (zero_lt_one.trans hw) j.1) (Real.rpow_pos_of_pos (zero_lt_one.trans hw) X)).mp
  rwa [Real.log_rpow (zero_lt_one.trans hw)]
end NumberTheoryLean.BoundedEdgePrimeRange



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_IsolatedRealPrimeRange
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedRealPrimeRange
open LogarithmicBinScale LogarithmicBinEndpoints PrimeBinRepresentatives IsolatedBinGeometry

theorem isolated_real_range {w top xi B alpha beta : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (hpower : w^B=top) {b : Fin (binCount w top xi)}
    (hb : isolatedBin w top xi B alpha beta b) :
    top^alpha ≤ lower w top xi b ∧ upper w top xi b ≤ top^beta := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have htop0 : 0 < top := hw0.trans htop
  have hlow : 0 < lower w top xi b := endpoint_pos hw0 _
  have hupp : 0 < upper w top xi b := hlow.trans (bin_source_bounds hw0 htop hxi b).2.1
  have hlog : Real.log top=B*Real.log w := by rw [← hpower,Real.log_rpow hw0]
  have hlo : alpha*B*Real.log w ≤ Real.log (lower w top xi b) :=
    (le_div_iff₀ (Real.log_pos hw)).mp hb.1
  have hhi : Real.log (upper w top xi b) ≤ beta*B*Real.log w :=
    (div_le_iff₀ (Real.log_pos hw)).mp hb.2
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos htop0 alpha) hlow).mp
    rw [Real.log_rpow htop0,hlog]
    nlinarith
  · apply (Real.log_le_log_iff hupp (Real.rpow_pos_of_pos htop0 beta)).mp
    rw [Real.log_rpow htop0,hlog]
    nlinarith
end NumberTheoryLean.IsolatedRealPrimeRange


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricInverseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricIsolatedBin
open PrimeHistories GeometricRegularWords GeometricBoxImages ActualWordSelection ActualRegularBoxes
open ErdosSubsetWord SafeSubsetBoxGeometry FirstIsolatedPosition IsolatedBinGeometry IsolatedRealPrimeRange
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_box_isolated_singleton {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hpower : w^B=top)
    (hsearch : w^((1/4:ℝ)) ≤ alpha*B) (z : Node)
    (m : Fin (binCount w top xi) → ℕ) (hm : m ∈ geometricBoxes hw htop hxi C B R L alpha beta z) :
    ∃ i : Fin (binCount w top xi),m i=1 ∧ isolatedBin w top xi B alpha beta i ∧ top^alpha ≤ lower w top xi i ∧
      upper w top xi i ≤ top^beta ∧ ActualSourceTags.searchBin w (lower w top xi i) := by
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨pre,p,tail,he,hisol,_hfirst⟩ := geometric_first_isolated hw htop hxi z ps hps
  have hrange := isolated_real_range hw htop hxi hpower hisol
  have hlo := hrange.1
  have hhi := hrange.2
  have hs := isolated_bin_search hisol hsearch
  let i := label (zero_lt_one.trans hw) htop hxi p
  have hp : p ∈ ps := by rw [he]; simp
  have hreg := (Finset.mem_filter.mp hps).1
  obtain ⟨hd,_hl,_hc,_hg,hsingle⟩ := Finset.mem_filter.mp hreg
  have hn : ps.Nodup := (mem_decreasingPrefixes.mp hd).1.imp (fun h => ne_of_gt h)
  have hcount : 0 < (ps.map (label (zero_lt_one.trans hw) htop hxi)).count i :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hle := hsingle i hs
  refine ⟨i,?_,hisol,hlo,hhi,hs⟩
  rw [wordMultiplicity_count _ ps hn]
  omega
end NumberTheoryLean.GeometricIsolatedBin



namespace NumberTheoryLean.GeometricBinOrdering
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints PrimeBinRepresentatives
open IsolatedBinGeometry BoundedEdgeBins BoundedEdgePrimeRange


theorem left_exponent_mono {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (i j : Fin (binCount w top xi)) (hij : i ≤ j) :
    leftExponent w (lower w top xi i) ≤ leftExponent w (lower w top xi j) := by
  have hlow := endpoint_mono (zero_lt_one.trans hw) htop hxi (show i.1 ≤ j.1 from hij)
  exact div_le_div_of_nonneg_right (Real.log_le_log (endpoint_pos (zero_lt_one.trans hw) i.1) hlow) (Real.log_pos hw).le

theorem isolated_before_bounded_edge {w top xi B alpha beta M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi))
    (hi : isolatedBin w top xi B alpha beta i) (hj : boundedEdgeBin w top xi Y m M X j)
    (hlarge : X < alpha*B) : j < i := by
  by_contra! hle
  have hh := left_exponent_mono hw htop hxi i j hle
  have hb := bounded_edge_lower_exponent hw htop hxi m j hj
  linarith [hi.1]
end NumberTheoryLean.GeometricBinOrdering



namespace NumberTheoryLean.GeometricInverseGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord GeometricBoxImages GeometricIsolatedBin
open GeometricBinOrdering BoundedEdgeBins BoundedEdgePrimeRange ParentCofactorChoices CofactorAllChoiceBounds
open SafeSubsetBoxGeometry BinCutSelections
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints


theorem geometric_inverse_geometry {w top xi B C K L alpha a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 1 ≤ C) (hlog : 1 ≤ Real.log w)
    (hcomp : Real.log B ≤ 2*Real.log w) (hDelta : 2*C*xi ≤ 1) (hB : 3 ≤ B)
    (hpower : w^B=top) (hsearch : w^((1/4:ℝ)) ≤ alpha*B) (hlarge : X < alpha*B)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B) (hclosed : z.closed=true)
    (m : Fin (binCount w top xi) → ℕ) (hm : m ∈ geometricBoxes hw htop hxi C B K L alpha (1/100) z) :
    ∃ i : Fin (binCount w top xi),m i=1 ∧ top^alpha ≤ lower w top xi i ∧ lower w top xi i ≤ top^((1:ℝ)/100) ∧
      ∀ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m M X j →
      i ≠ j ∧ m j=1 ∧
      parentCofactorMultiplicity m i j i=0 ∧ parentCofactorMultiplicity m i j j=0 ∧
      ((∑ k,parentCofactorMultiplicity m i j k : ℕ):ℝ) ≤ C*Real.log B ∧
      w ≤ lower w top xi j ∧ lower w top xi j ≤ w^X ∧
      (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
        ∀ p ∈ globalBins w top xi i,Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log w ≤ M+1) ∧
      (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
        ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
          a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)*(u:ℝ)))/Real.log w) := by
  obtain ⟨i,hmi,hisol,hilo,hihi,_hsearch⟩ := geometric_box_isolated_singleton hw htop hxi hpower hsearch z m hm
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have ha := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hlen := anchor_total_length hw htop hxi z m ha
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  refine ⟨i,hmi,hilo,(bin_source_bounds (zero_lt_one.trans hw) htop hxi i).2.1.le.trans hihi,?_⟩
  intro j hj
  have hji := isolated_before_bounded_edge hw htop hxi m i j hisol hj hlarge
  have hzero := cofactor_slots_zero m i j
  have htotal : ((∑ k,parentCofactorMultiplicity m i j k : ℕ):ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (cofactor_total_le m i j)).trans hlen
  have hrange := bounded_edge_prime_range hw htop hxi m j hj
  have hall := cofactor_all_choice_lengths hw htop hxi (by linarith : 0 ≤ C) hcomp Y hY z hroot
    hs hz hg hclosed hcap m ha i j hji hmi hj
  refine ⟨ne_of_gt hji,bounded_edge_singleton m j hj,hzero.1,hzero.2,htotal,hrange.1,hrange.2,?_,hall.2⟩
  intro q hq p hp
  exact (hall.1 q hq p hp).trans (by linarith)
end NumberTheoryLean.GeometricInverseGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_IsolatedPowerOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedPowerOrdering
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints PrimeBinRepresentatives
open GeometricBinOrdering BoundedEdgeBins BoundedEdgePrimeRange


theorem source_power_before_edge {w top xi B alpha M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hpower : w^B=top)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi))
    (hi : top^alpha ≤ lower w top xi i) (hj : boundedEdgeBin w top xi Y m M X j)
    (hlarge : X < alpha*B) : j < i := by
  have htop0 : 0 < top := (zero_lt_one.trans hw).trans htop
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos htop0 alpha) hi
  rw [Real.log_rpow htop0] at hlog
  have ht : Real.log top=B*Real.log w := by rw [← hpower,Real.log_rpow (zero_lt_one.trans hw)]
  rw [ht] at hlog
  have hlow : alpha*B ≤ leftExponent w (lower w top xi i) := by
    apply (le_div_iff₀ (Real.log_pos hw)).mpr
    nlinarith
  by_contra! hle
  have hh := left_exponent_mono hw htop hxi i j hle
  have hb := bounded_edge_lower_exponent hw htop hxi m j hj
  linarith
end NumberTheoryLean.IsolatedPowerOrdering


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_BoxWitnessFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.BoxWitnessFactorization
open ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling
open TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices BinCutSelections FourCoordinateBoxSum CanonicalSubsetBox

attribute [local instance] Classical.propDecidable

theorem witness_three_sum (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U W=∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*(if W (p,q) u then 1 else 0) := by
  unfold weightedWitness witnessPairs
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,tripleWeight]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro q _hq
  split_ifs <;> ring

theorem four_sum_descendants (P Q U D : Finset ℕ) (G : ℕ → ℕ → ℕ → ℝ) :
    (∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,∑ d ∈ D,
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p q u)=
      harmonicMass D*(∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p q u) := by
  have hh : ∀ p u q : ℕ,(∑ d ∈ D,((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p q u)=
      harmonicMass D*(((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p q u) := by
    intro p u q
    rw [harmonicMass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  simp_rw [hh]
  simp only [← Finset.mul_sum]

theorem selection_witness_factor {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (W : (ℕ × ℕ) → ℕ → Prop) :
    selectionWitnessMass P m i j W=
      harmonicMass (cofactorChoices P (belowMultiplicity m j))*
        weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W := by
  have hh := four_coordinate_sum P m hP hd i j hji hi hj (fun p u q _d => if W (p,q) u then (1:ℝ) else 0)
  have he : selectionWitnessMass P m i j W=
      ∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
        (if W (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) then 1 else 0) := by
    simp only [selectionWitnessMass,Finset.sum_filter,mul_ite,mul_one,mul_zero]
  rw [he,hh,four_sum_descendants,witness_three_sum]

theorem full_box_mass_factor {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) :
    selectionMass P m=harmonicMass (cofactorChoices P (belowMultiplicity m j))*
      (harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j)) := by
  have hh := selection_witness_factor P m hP hd i j hji hi hj (fun _ _ => True)
  have he : weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) (fun _ _ => True)=
      harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j) := by
    unfold weightedWitness witnessPairs
    simp only [Finset.filter_true_of_mem (fun _ _ => trivial)]
    exact triple_weight_sum _ _ _
  simpa only [selectionWitnessMass,Finset.filter_true_of_mem (fun _ _ => trivial),selectionMass,he] using hh
end NumberTheoryLean.BoxWitnessFactorization


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricRangeInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.NormalizedBoxException
open ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling CanonicalSubsetBox
open BoxWitnessFactorization ParentCofactorChoices BinCutSelections

attribute [local instance] Classical.propDecidable

theorem weighted_witness_le_total (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U W ≤ harmonicMass P*harmonicMass Q*harmonicMass U := by
  have hs : witnessPairs (P.product Q) U W ⊆ tripleSpace P Q U := Finset.filter_subset _ _
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ => tripleWeight_nonneg x)
  exact hh.trans_eq (triple_weight_sum P Q U)

theorem unnormalize_witness (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : weightedWitness P Q U W/(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma) :
    weightedWitness P Q U W ≤ sigma*(harmonicMass P*harmonicMass Q*harmonicMass U) := by
  have hm : 0 ≤ harmonicMass P*harmonicMass Q*harmonicMass U :=
    mul_nonneg (mul_nonneg (harmonicMass_nonneg P) (harmonicMass_nonneg Q)) (harmonicMass_nonneg U)
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm,mul_zero]
    have hh := weighted_witness_le_total P Q U W
    rwa [← hm] at hh
  · exact (div_le_iff₀ hm).mp h

theorem selection_exception_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (W : (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W/
      (harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j)) ≤ sigma) :
    selectionWitnessMass P m i j W ≤ sigma*selectionMass P m := by
  have hw := unnormalize_witness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W sigma h
  rw [selection_witness_factor P m hP hd i j hji hi hj,full_box_mass_factor P m hP hd i j hji hi hj]
  have hh := mul_le_mul_of_nonneg_left hw (harmonicMass_nonneg (cofactorChoices P (belowMultiplicity m j)))
  nlinarith
end NumberTheoryLean.NormalizedBoxException



namespace NumberTheoryLean.ActualInverseFullBoxMass
open ErdosInverseSampleCost ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling ErdosInverseBoxApplication
open NormalizedBoxException BoxWitnessFactorization CanonicalSubsetBox ParentCofactorChoices


theorem actual_inverse_full_box_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 S R Z cp sigma : ℝ) (F : ℕ)
    (hInv : SourceInverseConclusion Y small a delta V0 S R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j)) :
    selectionWitnessMass P m i j (actualWitness Y small a delta V0 (P i) S R Z cp) ≤ sigma*selectionMass P m := by
  have hh := hInv.2.2.1
  rw [actual_exception_weight] at hh
  exact selection_exception_bound P m hP hd i j hji hi hj _ sigma hh
end NumberTheoryLean.ActualInverseFullBoxMass



namespace NumberTheoryLean.GeometricRangeInverse
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages GeometricInverseGeometry BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale IsolatedSourceScales SourceNodeCoordinates
open ActualInverseFullBoxMass BoxWitnessFactorization CanonicalSubsetBox IsolatedPowerOrdering ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology


theorem geometric_range_inverse (C Kstar aStar alpha delta sigma : ℝ)
    (hC : 1 ≤ C) (hKstar : 0 ≤ Kstar) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi₀ : ℝ,0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < ErdosInverseBoxHeight.sourceW top,∃ htop : ErdosInverseBoxHeight.sourceW top < top,
      ∀ R L : ℝ,∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff=ErdosInverseBoxHeight.sourceB top → z.closed=true →
        z.gap=Real.log (ErdosInverseBoxHeight.sourceY top:ℝ)/Real.log (ErdosInverseBoxHeight.sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (ErdosInverseBoxHeight.sourceB top) R L alpha (1/100) z,
      ∃ i : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),m i=1 ∧
      top^alpha ≤ lower (ErdosInverseBoxHeight.sourceW top) top xi i ∧
      lower (ErdosInverseBoxHeight.sourceW top) top xi i ≤ top^((1:ℝ)/100) ∧
      ∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
        boundedEdgeBin (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m
          (2*Kstar+3) (2*Kstar+3) j → ∀ residue : ℕ → ℕ,
        j < i ∧ m j=1 ∧
        let cm := parentCofactorMultiplicity m i j
        let w := ErdosInverseBoxHeight.sourceW top
        SourceInverseConclusion (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊w⌋₊) (cofactorScale top xi cm)
          (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp sigma F
          (actualBins top xi i) (cofactorChoices (actualBins top xi) cm) (actualBins top xi j) ∧
        selectionWitnessMass (actualBins top xi) m i j
          (actualWitness (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊w⌋₊) (actualBins top xi i) (cofactorScale top xi cm)
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m := by
  obtain ⟨cp,hcp,F,xiI,hxiI,hxiI1,hInv⟩ := actual_source_inverse_jb247 C (2*Kstar+4) aStar (2*Kstar+3) alpha delta sigma
    (by linarith) (by linarith) ha ha1 (by linarith) halpha hd hsigma hsigma1
  have hC0 : 0 < C := by linarith
  refine ⟨cp,hcp,F,min xiI (1/(2*C)),lt_min hxiI (by positivity),(min_le_left _ _).trans hxiI1,?_⟩
  intro xi hxi hxi₀
  have hxI := hxi₀.trans (min_le_left _ _)
  have hDelta : 2*C*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp (hxi₀.trans (min_le_right _ _))
    nlinarith
  have hWT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hlargeT := (hBT.const_mul_atTop halpha).eventually_gt_atTop (2*Kstar+3)
  filter_upwards [hInv xi hxi hxI,ErdosCofactorChoices.source_span_geometry,
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually (source_isolated_search_scale halpha),
    hBT.eventually_ge_atTop 3,hWT.eventually_ge_atTop (Real.exp 1),hlargeT,
    eventually_gt_atTop (1:ℝ)] with top hInverse hspan hscale hsearch hB3 hWexp hlarge htop1
  change Real.exp 1 ≤ ErdosInverseBoxHeight.sourceW top at hWexp
  change 3 ≤ ErdosInverseBoxHeight.sourceB top at hB3
  change 2*Kstar+3 < alpha*ErdosInverseBoxHeight.sourceB top at hlarge
  have hw : 1 < ErdosInverseBoxHeight.sourceW top := hscale.1
  have htop : ErdosInverseBoxHeight.sourceW top < top := hspan.2.1
  have hlog : 1 ≤ Real.log (ErdosInverseBoxHeight.sourceW top) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hWexp
    simpa only [Real.log_exp] using hh
  have hpow : (ErdosInverseBoxHeight.sourceW top)^(ErdosInverseBoxHeight.sourceB top)=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  refine ⟨hw,htop,?_⟩
  intro R L z hi h199 hz hcut hclosed hroot m hm
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hY : 0 < ErdosInverseBoxHeight.sourceY top := by
    by_contra! hn
    have hzero : ErdosInverseBoxHeight.sourceY top=0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    have hg := node_gap_eq hs hz hcut
    nlinarith
  have hgeo := geometric_inverse_geometry (M:=2*Kstar+3) (X:=2*Kstar+3) hw htop hxi hC hlog hscale.2.2.2.2 hDelta hB3 hpow hsearch hlarge
    (ErdosInverseBoxHeight.sourceY top) hY z hroot hi h199 hz hcut hclosed m hm
  obtain ⟨i,hmi,hilo,hihi,hgeo⟩ := hgeo
  refine ⟨i,hmi,hilo,hihi,?_⟩
  intro j hj residue
  obtain ⟨hij,_hmj,hzi,hzj,hlen,_hUlo,hUhi,hparent,hchild⟩ := hgeo j hj
  have hji := source_power_before_edge hw htop hxi hpow m i j hilo hj hlarge
  have hmj := bounded_edge_singleton m j hj
  refine ⟨hji,hmj,?_⟩
  dsimp only
  have hresult := hInverse (parentCofactorMultiplicity m i j) i j hij hzi hzj hlen residue hilo hihi hUhi
    (by
      intro q hq p hp
      change Real.log ((ErdosInverseBoxHeight.sourceY top:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log (ErdosInverseBoxHeight.sourceW top) ≤ _
      have hh := hparent q hq p hp
      nlinarith)
    (by
      intro q hq p hp u hu
      exact (by linarith : 3*aStar/4 ≤ aStar).trans (hchild q hq p hp u hu))
  refine ⟨hresult,?_⟩
  exact actual_inverse_full_box_mass (actualBins top xi) m
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
    (fun k l hkl => LogarithmicBinPartition.bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    i j hji hmi hmj _ _ residue _ _ _ _ _ _ _ F hresult
end NumberTheoryLean.GeometricRangeInverse


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CandidateExceptionMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MultiplicitySuffixRank
open BinCutSelections

attribute [local instance] Classical.propDecidable

theorem below_total_rank {n : ℕ} (m : Fin n → ℕ) (j : Fin n) :
    1+∑ k,belowMultiplicity m j k=suffixRank m j := by
  simp only [suffixRank,lowerIndices,Finset.sum_filter,belowMultiplicity]

theorem suffixRank_pos {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : 0 < suffixRank m j := by
  unfold suffixRank
  omega

theorem suffixRank_strict {n : ℕ} (m : Fin n → ℕ) (j k : Fin n) (hjk : j<k) (hmj : 0 < m j) :
    suffixRank m j < suffixRank m k := by
  have hnot : j ∉ lowerIndices j := by simp [lowerIndices]
  have hsub : insert j (lowerIndices j) ⊆ lowerIndices k := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp [lowerIndices,hjk]
    · have hh := (Finset.mem_filter.mp hb).2
      simp [lowerIndices,hh.trans hjk]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => Nat.zero_le (m b))
  rw [Finset.sum_insert hnot] at hsum
  unfold suffixRank
  omega

theorem suffixRank_injective_singletons {n : ℕ} (m : Fin n → ℕ) :
    Set.InjOn (suffixRank m) {j | m j=1} := by
  intro j hj k hk he
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hh := suffixRank_strict m j k hjk (by change m j=1 at hj; omega)
    omega
  · rfl
  · have hh := suffixRank_strict m k j hkj (by change m k=1 at hk; omega)
    omega

theorem singleton_card_le_rank {n : ℕ} (m : Fin n → ℕ) (J : Finset (Fin n)) (H : ℕ)
    (hm : ∀ j ∈ J,m j=1) (hH : ∀ j ∈ J,suffixRank m j ≤ H) : J.card ≤ H := by
  have hinj : Set.InjOn (suffixRank m) (J : Set (Fin n)) :=
    fun j hj k hk he => suffixRank_injective_singletons m (hm j hj) (hm k hk) he
  have hsub : J.image (suffixRank m) ⊆ Finset.Icc 1 H := by
    intro r hr
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Icc.mpr ⟨suffixRank_pos m j,hH j hj⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  simpa using hh
end NumberTheoryLean.MultiplicitySuffixRank



namespace NumberTheoryLean.BoundedEdgeSuffixRank
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport StrongSourceFamilies
open ErdosCofactorChoices ErdosSubsetWord BoundedEdgeBins FullBoxLengthBounds BinCutSelections SelectionWordSplit
open MultiplicitySuffixRank SafeSubsetBoxGeometry RepresentativeAdmission
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem list_length_le_exponents (w : ℝ) (ps : List ℕ) (hp : ∀ p ∈ ps,1 ≤ primeExponent w p) :
    (ps.length:ℝ) ≤ (ps.map (primeExponent w)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hh := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    have hp1 := hp p (by simp)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons]
    linarith

theorem bounded_edge_rank_le {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (ha0 : 0 ≤ a) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (j : Fin (binCount w top xi)) (hj : boundedEdgeBin w top xi Y m M X j) :
    suffixRank m j ≤ ⌈M⌉₊ := by
  obtain ⟨f,hf,u,hfu,hparent,_hx⟩ := hj
  have hword := selected_word_split hw htop hxi m f hf j u hfu
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap _ hfull).2
  have hsource := word_source_membership hw htop hxi m f hf
  have hsuffix : ∀ p ∈ u::descendingWord (belowSelection f j),1 ≤ primeExponent w p := by
    intro p hp
    have hpfull : p ∈ descendingWord f := by rw [hword]; exact List.mem_append_right _ hp
    have hpw := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hpfull)
    change 1 ≤ Real.log (p:ℝ)/Real.log w
    exact ((one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hpw.2.1)).le
  have hlength := list_length_le_exponents w (u::descendingWord (belowSelection f j)) hsuffix
  have hgap : (terminal w z (descendingWord f)).gap=
      (terminal w z (descendingWord (aboveSelection f j))).gap-
        ((u::descendingWord (belowSelection f j)).map (primeExponent w)).sum := by
    rw [hword,terminal_append]
    exact terminal_gap_sum w _ _
  have hpar := parent_length_gap hw htop hxi Y hY z hroot m f hf j
  have hrank : suffixRank m j=(u::descendingWord (belowSelection f j)).length := by
    rw [← below_total_rank,List.length_cons,global_word_length hw htop hxi _ _ (below_selection_mem _ m f hf j)]
    omega
  have hreal : (suffixRank m j:ℝ) ≤ M := by rw [hrank]; nlinarith
  exact_mod_cast (hreal.trans (Nat.le_ceil M))
end NumberTheoryLean.BoundedEdgeSuffixRank



namespace NumberTheoryLean.BoundedCandidateCount
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry GeometricBoxImages BoundedEdgeBins BoundedEdgeSuffixRank MultiplicitySuffixRank
open LogarithmicBinScale LogarithmicBinLabels

attribute [local instance] Classical.propDecidable

theorem candidate_bins_card_le {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (ha0 : 0 ≤ a) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m) :
    (candidateBins w top xi Y m M X).card ≤ ⌈M⌉₊ := by
  apply singleton_card_le_rank m _ _
  · intro j hj
    exact bounded_edge_singleton m j (Finset.mem_filter.mp hj).2
  · intro j hj
    exact bounded_edge_rank_le hw htop hxi hC hcomp ha0 Y hY z hroot hs hz hg hclosed hcap m ha j (Finset.mem_filter.mp hj).2
end NumberTheoryLean.BoundedCandidateCount



namespace NumberTheoryLean.CandidateExceptionMass
open ErdosCofactorChoices BoxWitnessFactorization CanonicalSubsetBox TwoPrimeObservableSum ParentTailPartition

attribute [local instance] Classical.propDecidable

theorem some_witness_mass_le_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) :
    someWitnessMass P m i J W ≤ ∑ j ∈ J,selectionWitnessMass P m i j (W j) := by
  simp only [someWitnessMass,selectionWitnessMass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro f _hf
  have hn : 0 ≤ (selectionProduct f:ℝ)⁻¹ := by positivity
  by_cases hex : ∃ j∈J,W j (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)
  · rw [ite_eq_left hex]
    obtain ⟨j,hj,hw⟩ := hex
    have hh := Finset.single_le_sum (fun k _hk =>
      show 0 ≤ if W k (pickedPrime f i,selectionProduct (parentCofactorSelection f i k)) (pickedPrime f k) then (selectionProduct f:ℝ)⁻¹ else 0 from by split_ifs <;> positivity) hj
    simpa only [ite_eq_left hw] using hh
  · rw [ite_eq_right hex]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)

theorem some_witness_mass_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ)
    (h : ∀ j∈J,selectionWitnessMass P m i j (W j) ≤ sigma*selectionMass P m) :
    someWitnessMass P m i J W ≤ (J.card:ℝ)*sigma*selectionMass P m := by
  have hh := (some_witness_mass_le_sum P m i J W).trans (Finset.sum_le_sum h)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

theorem some_witness_mass_card_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (H : ℕ) (hcard : J.card ≤ H)
    (h : ∀ j∈J,selectionWitnessMass P m i j (W j) ≤ sigma*selectionMass P m) :
    someWitnessMass P m i J W ≤ (H:ℝ)*sigma*selectionMass P m := by
  have hm : 0 ≤ selectionMass P m := Finset.sum_nonneg (fun _ _ => by positivity)
  have hc : (J.card:ℝ) ≤ H := by exact_mod_cast hcard
  exact (some_witness_mass_bound P m i J W sigma h).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hsigma) hm)
end NumberTheoryLean.CandidateExceptionMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceRawBoxFactory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricCandidateCount
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open SafeSubsetBoxGeometry GeometricBoxImages BoundedCandidateCount
open LogarithmicBinScale LogarithmicBinLabels

theorem geometric_candidate_card {w top xi B C K L alpha beta a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 1 ≤ C) (hlog : 1 ≤ Real.log w)
    (hcomp : Real.log B ≤ 2*Real.log w) (hB : 3 ≤ B) (ha0 : 0 ≤ a)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B) (hclosed : z.closed=true)
    (hpower : w^B=top) (m : Fin (binCount w top xi) → ℕ)
    (hm : m ∈ geometricBoxes hw htop hxi C B K L alpha beta z) :
    (candidateBins w top xi Y m M X).card ≤ ⌈M⌉₊ := by
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hA := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  exact candidate_bins_card_le hw htop hxi (by linarith) hcomp ha0 Y hY z hroot hs hz hg hclosed hcap m hA
end NumberTheoryLean.GeometricCandidateCount



namespace NumberTheoryLean.GeometricRangeCandidateUnion
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages GeometricInverseGeometry BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale IsolatedSourceScales SourceNodeCoordinates
open GeometricRangeInverse GeometricCandidateCount CandidateExceptionMass BoundedCandidateCount
open ActualInverseFullBoxMass BoxWitnessFactorization CanonicalSubsetBox IsolatedPowerOrdering ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem geometric_range_candidate_union_jb247_oai (C Kstar aStar alpha delta sigma : ℝ)
    (hC : 1 ≤ C) (hKstar : 0 ≤ Kstar) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi₀ : ℝ,0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < ErdosInverseBoxHeight.sourceW top,∃ htop : ErdosInverseBoxHeight.sourceW top < top,
      ∀ R L : ℝ,∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff=ErdosInverseBoxHeight.sourceB top → z.closed=true →
        z.gap=Real.log (ErdosInverseBoxHeight.sourceY top:ℝ)/Real.log (ErdosInverseBoxHeight.sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (ErdosInverseBoxHeight.sourceB top) R L alpha (1/100) z,
      ∃ i : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),m i=1 ∧
      top^alpha ≤ lower (ErdosInverseBoxHeight.sourceW top) top xi i ∧
      lower (ErdosInverseBoxHeight.sourceW top) top xi i ≤ top^((1:ℝ)/100) ∧
      (∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
        boundedEdgeBin (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m
          (2*Kstar+3) (2*Kstar+3) j → ∀ residue : ℕ → ℕ,
        j < i ∧ m j=1 ∧
        let cm := parentCofactorMultiplicity m i j
        let w := ErdosInverseBoxHeight.sourceW top
        SourceInverseConclusion (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊w⌋₊) (cofactorScale top xi cm)
          (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp sigma F
          (actualBins top xi i) (cofactorChoices (actualBins top xi) cm) (actualBins top xi j) ∧
        selectionWitnessMass (actualBins top xi) m i j
          (actualWitness (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊w⌋₊) (actualBins top xi i) (cofactorScale top xi cm)
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m ) ∧ ∀ residue : ℕ → ℕ,
        someWitnessMass (actualBins top xi) m i
          (candidateBins (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m (2*Kstar+3) (2*Kstar+3))
          (fun j => actualWitness (ErdosInverseBoxHeight.sourceY top)
            (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊) (actualBins top xi i)
            (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (ErdosInverseBoxHeight.sourceW top) top xi i)
            (ErdosInverseBoxHeight.sourceZ top) cp) ≤ (⌈2*Kstar+3⌉₊:ℝ)*sigma*selectionMass (actualBins top xi) m := by
  obtain ⟨cp,hcp,F,xi₀,hxi₀,hxi₀1,hCore⟩ := geometric_range_inverse C Kstar aStar alpha delta sigma
    hC hKstar ha ha1 halpha hd hsigma hsigma1
  refine ⟨cp,hcp,F,xi₀,hxi₀,hxi₀1,?_⟩
  intro xi hxi hx
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hCore xi hxi hx,hBT.eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually source_scale_eventually,ErdosInverseBoxHeight.source_B_bounds]
    with top hCore hB3 hscale hbounds
  obtain ⟨hw,htop,hData⟩ := hCore
  change 3 ≤ ErdosInverseBoxHeight.sourceB top at hB3
  have hlog : 1 ≤ Real.log (ErdosInverseBoxHeight.sourceW top) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hbounds.1
    simpa only [Real.log_exp] using hh
  have hpow : (ErdosInverseBoxHeight.sourceW top)^(ErdosInverseBoxHeight.sourceB top)=top :=
    (sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  refine ⟨hw,htop,?_⟩
  intro R L z hi h199 hz hcut hclosed hroot m hm
  obtain ⟨i,hmi,hilo,hihi,hStep⟩ := hData R L z hi h199 hz hcut hclosed hroot m hm
  refine ⟨i,hmi,hilo,hihi,hStep,?_⟩
  intro residue
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hY : 0 < ErdosInverseBoxHeight.sourceY top := by
    by_contra! hn
    have hzero : ErdosInverseBoxHeight.sourceY top=0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    have hg := node_gap_eq hs hz hcut
    nlinarith
  have hCard := geometric_candidate_card (M:=2*Kstar+3) (X:=2*Kstar+3) hw htop hxi hC hlog hscale.2.2.2.2
    hB3 ha.le (ErdosInverseBoxHeight.sourceY top) hY z hroot hi h199 hz hcut hclosed hpow m hm
  apply some_witness_mass_card_bound _ _ _ _ _ sigma hsigma.le _ hCard
  intro j hj
  exact (hStep j (Finset.mem_filter.mp hj).2 residue).2.2.2
end NumberTheoryLean.GeometricRangeCandidateUnion



open _root_.Filter


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247_oai := @OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247_oai
