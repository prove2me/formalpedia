-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.SourceCompactErrorMass.source_compact_error_mass_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:09:00.08093+00:00
-- url     : https://prove2.me/submissions/261d7ece-cd54-486b-8f83-dad9e181665f

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
import Theorems.Thm_OAI_Erdos970_ErdosVarianceFactory_source_raw_box_factory_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_GeometricTotalBoxMass_uniform_geometric_box_mass_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_PaperMissingPrimeWindow_paper_missing_prime_window_mass_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_PaperRegularTagCapture_paper_regular_bad_tag_mass_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_UniformGeometricRegularMass_geometric_defect_uniform_in_L_jb247

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



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

end ErdosPrimeInputs.PrimePrefixTail



end Erdos970

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

end NumberTheoryLean.ReferencePrefixRecurrence

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

theorem actual_mark_to_representative_window {b₀ b₁ r rrep x xrep Delta h : ℝ}
    (hb₀ : 0 < b₀) (hx₀ : 2*b₀ ≤ x) (hx₁ : x ≤ b₁/2)
    (hxr : x ≤ xrep) (hxh : xrep ≤ x+h)
    (hr : rrep ≤ r) (hrD : r ≤ rrep+Delta)
    (hs₀ : 208/100 ≤ r/x) (hs₁ : r/x ≤ 214/100)
    (hh : h ≤ b₀) (hsmall : Delta+(206/100)*h ≤ (4/100)*b₀) :
    b₀ ≤ xrep ∧ xrep ≤ b₁ ∧ 206/100 ≤ rrep/xrep ∧ rrep/xrep ≤ 216/100 := by
  have hx : 0 < x := by linarith
  have hxp : 0 < xrep := hx.trans_le hxr
  have hlow := (le_div_iff₀ hx).mp hs₀
  have hhigh := (div_le_iff₀ hx).mp hs₁
  refine ⟨by linarith,by linarith,?_,?_⟩
  · apply (le_div_iff₀ hxp).mpr
    nlinarith
  · apply (div_le_iff₀ hxp).mpr
    nlinarith

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

theorem after_node (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).node = terminal w v.node ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => exact ih (child w v p)

theorem after_past (w : ℝ) (v : Vertex) (ps : List ℕ) :
    (after w v ps).past = v.past++ps := by
  induction ps generalizing v with
  | nil => simp [after]
  | cons p ps ih =>
    change (after w (child w v p) ps).past = _
    rw [ih]
    simp [child,List.append_assoc]

theorem prefixWeight_product (ps : List ℕ) : prefixWeight ps = ((ps.prod:ℕ):ℝ)⁻¹ := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    change (p:ℝ)⁻¹*prefixWeight ps = ((p*ps.prod:ℕ):ℝ)⁻¹
    rw [ih,Nat.cast_mul,mul_inv_rev]
    ring

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.FirstStopSemantics

open _root_.Finset
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem firstStop_nil (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (hs : lowerStop stop v) :
    FirstStop w stop v [] := by
  refine ⟨hs,?_⟩
  intro pre tail heq ht
  exact False.elim (ht (List.append_eq_nil_iff.mp heq.symm).2)

theorem stopped_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : FirstStop w stop v ps := by
  induction n generalizing v ps with
  | zero =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · exact False.elim (Finset.notMem_empty _ hp)
  | succ n ih =>
    unfold stopped at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · have heq : ps = [] := Finset.mem_singleton.mp hp
      subst ps
      exact firstStop_nil w stop v hs
    · obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      have hfirst := ih (child w v p) ht
      refine ⟨hfirst.1,?_⟩
      intro pre suffix heq hsuffix
      cases pre with
      | nil => exact hs
      | cons q qs =>
        rw [List.cons_append] at heq
        have hhead := (List.cons.inj heq).1
        have htail := (List.cons.inj heq).2
        subst q
        exact hfirst.2 qs suffix htail hsuffix

end NumberTheoryLean.FirstStopSemantics



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

end NumberTheoryLean.StoppedTraceAdmission



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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedSourceSmallness

open _root_.Filter
open scoped Topology
open ExponentialMesh

theorem moving_compact_gap_small (R : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, R < 6*(K*(Real.log w)^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (1:ℝ) (1+R/(6*K))))] with w hw
  have hL : 1 ≤ Real.log w := (le_max_left _ _).trans hw
  have hR : 1+R/(6*K) ≤ Real.log w := (le_max_right _ _).trans hw
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*K by positivity)
  have he : 6*K*(1+R/(6*K)) = 6*K+R := by field_simp [hK.ne']
  rw [he] at hm
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 6*K by positivity)
  nlinarith

end NumberTheoryLean.MarkedSourceSmallness

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_MovingStopMargins
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StoppedTraceMembership
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedEvaluation
open StoppedTraceSets StoppedTraceAdmission FirstStopSemantics ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_cons_iff (w : ℝ) (v : Vertex) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w v.available v.node.side v.node.gap ↔
    p ∈ includedPrimes w v ∧ ps ∈ referencePrefixes w (child w v p).available
      (child w v p).node.side (child w v p).node.gap := by
  constructor
  · intro h
    obtain ⟨hD,hA⟩ := Finset.mem_filter.mp h
    have hp := (mem_decreasingPrefixes.mp hD).2 p (by simp)
    have htail := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp hD
    refine ⟨Finset.mem_filter.mpr ⟨hp,hA.1⟩,Finset.mem_filter.mpr ⟨?_,hA.2⟩⟩
    simpa only [suffixPrimes,List.mem_singleton,forall_eq,child] using htail
  · rintro ⟨hp,hps⟩
    exact reference_child_cons w v hp hps

end NumberTheoryLean.StoppedTraceMembership

end

section

namespace NumberTheoryLean.TagBelowStopWindow
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment

theorem moving_window_below_search (rho K : ℝ) (hrho : 0 < rho) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,rho*K*(Real.log w)^2 < w^((1/4:ℝ)) := by
  have hC : 0 < rho*K := mul_pos hrho hK
  have hh := (isLittleO_log_rpow_rpow_atTop (s := (1/4:ℝ)) 2 (by norm_num)).bound
    (by positivity : (0:ℝ)<1/(2*(rho*K)))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with w hw hw0
  have hp : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos hw0 _
  rw [Real.rpow_two,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),abs_of_pos hp] at hw
  have hm := mul_le_mul_of_nonneg_left hw hC.le
  have he : (rho*K)*(1/(2*(rho*K))*w^((1/4:ℝ))) = w^((1/4:ℝ))/2 := by field_simp
  rw [he] at hm
  exact hm.trans_lt (by linarith)

end NumberTheoryLean.TagBelowStopWindow

end

section

namespace NumberTheoryLean.StoppedPrefixExistence
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedTraceSets StoppedTraceMembership
open ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem reference_length_le_card (w : ℝ) (v : Vertex) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w v.available v.node.side v.node.gap) : ps.length ≤ v.available.card := by
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  have hn : ps.Nodup := hd.1.imp (fun h => ne_of_gt h)
  have hsub : ps.toFinset ⊆ v.available := fun p hp => hd.2 p (List.mem_toFinset.mp hp)
  have hh := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn] using hh

theorem exists_stopped_prefix (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) (ps : List ℕ)
    (hlen : ps.length ≤ n) (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hhit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w v pre)) :
    ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w stop n v := by
  induction ps generalizing n v with
  | nil =>
    obtain ⟨pre,tail,heq,hs⟩ := hhit
    have hp : pre=[] := (List.append_eq_nil_iff.mp heq.symm).1
    subst pre
    refine ⟨[],[],rfl,?_⟩
    cases n <;> simp [stopped,traces,show lowerStop stop v from hs]
  | cons p ps ih =>
    by_cases hs : lowerStop stop v
    · refine ⟨[],p::ps,rfl,?_⟩
      cases n <;> simp [stopped,traces,hs]
    · obtain ⟨hp,htail⟩ := (reference_cons_iff w v p ps).mp href
      have hchildHit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w (child w v p) pre) := by
        obtain ⟨pre,tail,heq,hstop⟩ := hhit
        cases pre with
        | nil => exact False.elim (hs hstop)
        | cons q pre =>
          rw [List.cons_append] at heq
          have he := List.cons.inj heq
          have hehead := he.1
          subst q
          exact ⟨pre,tail,he.2,hstop⟩
      cases n with
      | zero => simp at hlen
      | succ n =>
        obtain ⟨pre,tail,heq,hpre⟩ := ih n (child w v p) (by simpa using hlen) htail hchildHit
        refine ⟨p::pre,tail,by simp only [List.cons_append,heq],?_⟩
        simp only [stopped,traces,hs,ite_false, if_false]
        exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨pre,hpre,rfl⟩⟩

theorem reference_candidate_forces_stop (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ)
    (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hhit : ∃ pre tail : List ℕ,ps=pre++tail ∧ lowerStop stop (after w v pre)) :
    ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w stop v.available.card v :=
  exists_stopped_prefix w stop v.available.card v ps (reference_length_le_card w v ps href) href hhit
end NumberTheoryLean.StoppedPrefixExistence

end

section

namespace NumberTheoryLean.MovingStopMargins
open _root_.Filter MarkedSourceSmallness TagBelowStopWindow

theorem moving_stop_margins (Cs Clen xi : ℝ) (hxi : 0 < xi)
    {rho K : ℝ} (hrho : 0 < rho) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ 1 ≤ Real.log w ∧
      0 < K*(Real.log w)^2 ∧ Cs < 2*(K*(Real.log w)^2) ∧
      rho*K*(Real.log w)^2 < w^((1/4:ℝ)) ∧
      xi/Real.log w ≤ K*(Real.log w)^2 ∧
      2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*(K*(Real.log w)^2) ∧
      ∀ B : ℝ,w ≤ B → (rho*K*(Real.log w)^2)/2 < B := by
  let M := max xi (max (Cs+1) (max 1 (25*(2*Clen*xi+(206/100)*xi)+1)))
  filter_upwards [moving_compact_gap_small (6*M) hK,
    moving_window_below_search rho K hrho hK,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hm hs hlog hw
  have hb : M < K*(Real.log w)^2 := by linarith
  have hxiM : xi ≤ M := le_max_left _ _
  have hCsM : Cs+1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hOneM : 1 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNumM : 25*(2*Clen*xi+(206/100)*xi)+1 ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hdiv : xi/Real.log w ≤ xi := div_le_self hxi.le hlog
  refine ⟨hw,hlog,by linarith,by linarith,hs,by linarith,by linarith,?_⟩
  intro B hB
  have hpow : w^((1/4:ℝ)) ≤ w := by
    calc
      _ ≤ w^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hw.le (by norm_num)
      _ = w := Real.rpow_one w
  have hb₁ : 0 < rho*K*(Real.log w)^2 := by positivity
  linarith
end NumberTheoryLean.MovingStopMargins

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

private theorem tagFrom_none (n : ℕ) (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ)
    (h : ∀ p ∈ ps,F p=none) : firstTagFrom F k ps=none := by
  induction ps generalizing k with
  | nil => rfl
  | cons p ps ih =>
    rw [firstTagFrom,h p (by simp)]
    exact ih (k+1) (fun q hq => h q (by simp [hq]))

theorem tagFrom_append_none (n : ℕ) (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (pre tail : List ℕ)
    (h : ∀ p ∈ tail,F p=none) : firstTagFrom F k (pre++tail)=firstTagFrom F k pre := by
  induction pre generalizing k with
  | nil => exact tagFrom_none n F k tail h
  | cons p pre ih =>
    simp only [List.cons_append,firstTagFrom]
    cases hp : F p with
    | none => exact ih (k+1)
    | some bq => rfl

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

theorem prefix_exponent_lower {w : ℝ} (hw : 1 < w) (z : Node) (pre : List ℕ) (hne : pre ≠ [])
    (hD : pre.Pairwise (· > ·)) (hp : ∀ p ∈ pre,p.Prime) :
    ∀ p ∈ pre,(terminal w z pre).cutoff ≤ primeExponent w p := by
  let last := pre.getLast hne
  have hlast : last ∈ pre := List.getLast_mem hne
  have he : pre.dropLast++[last]=pre := List.dropLast_append_getLast hne
  have hdc : (pre.dropLast++[last]).Pairwise (· > ·) := by rwa [he]
  intro p hpre
  have hlp : last ≤ p := by
    have hm : p ∈ pre.dropLast++[last] := by rwa [he]
    rcases List.mem_append.mp hm with hm | hm
    · exact ((List.pairwise_append.mp hdc).2.2 p hm last (by simp)).le
    · have hh : p=last := Finset.mem_singleton.mp (by simpa using hm)
      exact hh.symm.le
  rw [terminal_cutoff_last w z pre hne]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast (hp last hlast).pos)
    (by exact_mod_cast hlp)) (Real.log_pos hw).le

theorem suffix_exponent_upper {w : ℝ} (hw : 1 < w) (z : Node) (pre tail : List ℕ) (hne : pre ≠ [])
    (hD : (pre++tail).Pairwise (· > ·)) (hp : ∀ p ∈ pre++tail,p.Prime) :
    ∀ p ∈ tail,primeExponent w p < (terminal w z pre).cutoff := by
  intro p hpt
  have hl := List.getLast_mem hne
  have hlt : p < pre.getLast hne := (List.pairwise_append.mp hD).2.2 _ hl p hpt
  rw [terminal_cutoff_last w z pre hne]
  exact div_lt_div_of_pos_right (Real.log_lt_log (by exact_mod_cast (hp p (by simp [hpt])).pos)
    (by exact_mod_cast hlt)) (Real.log_pos hw)

theorem no_candidate_below_search {n : ℕ} (Y w Cs eta : ℝ) (hw : 1 < w)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℤ)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b) (p : ℕ)
    (hx : primeExponent w p < w^((1/4:ℝ))) : tagCandidate Y w Cs eta lower width label a p=none := by
  cases ht : tagCandidate Y w Cs eta lower width label a p with
  | none => rfl
  | some bq =>
    rcases bq with ⟨b,q⟩
    have hh := candidate_witness Y w Cs eta lower width label a p ht
    have hlow := (bin_exponent_bounds hw (hlo _) (hwidth _) hh.2.1).1
    have hs := hh.2.2.1
    change w^((1/4:ℝ)) ≤ leftExponent w (lower (label p)) at hs
    exact False.elim ((not_lt_of_ge hs) (hlow.trans hx))

theorem sourceTag_prefix_eq {n : ℕ} (Y w Cs eta : ℝ) (hw : 1 < w)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℤ)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b) (pre tail : List ℕ)
    (htail : ∀ p ∈ tail,primeExponent w p < w^((1/4:ℝ))) :
    sourceTag Y w Cs eta lower width label a (pre++tail)=sourceTag Y w Cs eta lower width label a pre := by
  exact tagFrom_append_none n _ 0 pre tail (fun p hp =>
    no_candidate_below_search Y w Cs eta hw lower width label a hlo hwidth p (htail p hp))
end NumberTheoryLean.MarkedPrefixTools

end

section

namespace NumberTheoryLean.MarkedPrefixCandidate
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ActualSourceTags FiniteFirstTag MarkedPrefixTools SuccessfulMarkedCoordinates
open ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem marked_prefix_candidate (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀)
    (hsearch : b₁ < w^((1/4:ℝ))) (hh : xi/Real.log w ≤ b₀)
    (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (a : ℕ → ℕ) (z : Node) (ps pre tail : List ℕ) (heq : ps=pre++tail)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (href : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hsafe : representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) ps)
    (t : Tag (binCount w top xi))
    (htag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t)
    (hcount : (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1)
    (halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p)
    (hwin : primeWindow b₀ b₁ (terminal w z pre)) :
    (terminal w z pre).side=.even ∧
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z pre := by
  let lab := label (zero_lt_one.trans hw) htop hxi
  let rep := representative w (lower w top xi) (width w top xi) lab
  have hne : pre ≠ [] := by
    intro hn
    have hh := hwin.2.2.2.2.1
    rw [hn,terminal_nil] at hh
    linarith
  have hsub : ∀ p ∈ pre,p ∈ ps := by
    intro p hp
    rw [heq]
    exact List.mem_append.mpr (Or.inl hp)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  have hdFull : (pre++tail).Pairwise (· > ·) := by simpa only [← heq] using hd.1
  have hdPre := (List.pairwise_append.mp hdFull).1
  have hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top := hd.2
  have hsourcePre : ∀ p ∈ pre,p ∈ sourcePrimeSet w top := fun p hp => hsource p (hsub p hp)
  have hprimes : ∀ p ∈ pre++tail,p.Prime := by
    intro p hp
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p (by rwa [heq]))).1
  have hprimesPre : ∀ p ∈ pre,p.Prime := fun p hp => hprimes p (by simp [hp])
  have hlenPre : (pre.length:ℝ) ≤ Clen*Real.log B := by
    have hh : pre.length ≤ ps.length := by rw [heq,List.length_append]; omega
    exact (by exact_mod_cast hh : (pre.length:ℝ) ≤ ps.length).trans hlen
  have hb₁ : 0 < b₁ := by linarith [hwin.2.2.2.1,hwin.2.2.2.2.1]
  have htailSmall : ∀ p ∈ tail,primeExponent w p < w^((1/4:ℝ)) := by
    intro p hp
    have hh := suffix_exponent_upper hw z pre tail hne hdFull hprimes p hp
    linarith [hwin.2.2.2.2.1]
  have htEq := sourceTag_prefix_eq Y w Cs eta hw (lower w top xi) (width w top xi) lab (sourceClass a)
    (fun b => endpoint_pos (zero_lt_one.trans hw) _) (fun b => (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le)
    pre tail htailSmall
  have htagPre : sourceTag Y w Cs eta (lower w top xi) (width w top xi) lab (sourceClass a) pre=some t := by
    apply htEq.symm.trans
    simpa only [← heq] using htag
  have hcountPre : (pre.map lab).count t.bin=1 := by
    obtain ⟨u,p,v,hpre,_hidx,hbin,_hp,_hs,_ho,_ha,_hn⟩ :=
      sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi) lab (sourceClass a) pre htagPre
    have hp : p ∈ pre := by rw [hpre]; simp
    have hm : t.bin ∈ pre.map lab := List.mem_map.mpr ⟨p,hp,hbin.symm⟩
    have hc := List.count_pos_iff.mpr hm
    change (ps.map lab).count t.bin=1 at hcount
    rw [heq,List.map_append,List.count_append] at hcount
    omega
  have halignPre : ∀ p ∈ pre,aligns (sourceClass a) t.rational p := by
    intro p hp
    have hh := prefix_exponent_lower hw z pre hne hdPre hprimesPre p hp
    exact halign p (hsub p hp) (by linarith [hwin.2.2.2.1])
  have hsafePre : representativeSafe w rep z (2*Clen*xi) pre := by
    intro qs hqs hneq heven
    have hpre : pre <+: ps := ⟨tail,heq.symm⟩
    have hall := (List.mem_inits _ _).mp hqs |>.trans hpre
    exact hsafe qs ((List.mem_inits _ _).mpr hall) hneq heven
  have hrefPre : pre ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
    apply Finset.mem_filter.mpr
    have hdecfull : pre ++ tail ∈ decreasingPrefixes (sourcePrimeSet w top) := by
      simpa only [← heq] using (Finset.mem_filter.mp href).1
    refine ⟨decreasing_prefix_mem (pre := pre) (suf := tail) hdecfull,?_⟩
    exact ((admitted_append w z.gap z.side pre tail).mp (by simpa only [← heq] using (Finset.mem_filter.mp href).2)).1
  have htr := source_reference_transport hw htop z hs hz hg hclosed hcap pre hrefPre
  obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w 1 z pre).mp ((mem_uncappedPrefixes hw z pre).mp htr.1)
  have hr0 : 0 < z.gap := by linarith [hg.1]
  have hn := terminal_consistent (by norm_num : (0:ℝ)≤1) hr0 hs hz hU
  have hxpos : 0 < (terminal w z pre).cutoff := by linarith [hwin.2.2.2.1]
  have hspos : 0 < (terminal w z pre).ratio := by linarith [hwin.2.1]
  have hratio : (terminal w z pre).gap/(terminal w z pre).cutoff=(terminal w z pre).ratio := by
    apply (div_eq_iff hxpos.ne').mpr
    have hh := (eq_div_iff hspos.ne').mp hn
    nlinarith
  have hlast : pre.getLastD 0 ∈ pre := by
    have hh : pre.getLastD 0=pre.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [hh]
    exact List.getLast_mem hne
  have hxerr := source_representative_error hw htop hxi (hsourcePre _ hlast)
  change 0 ≤ rep (pre.getLastD 0)-primeExponent w (pre.getLastD 0) ∧
    rep (pre.getLastD 0)-primeExponent w (pre.getLastD 0) ≤ xi/Real.log w at hxerr
  rw [← terminal_lastD w z pre hne] at hxerr
  have hm := source_prefix_movement hw htop hxi hC hcomp z pre hsourcePre hlenPre
  change 0 ≤ (terminal w z pre).gap-representativeGap rep z.gap pre ∧
    (terminal w z pre).gap-representativeGap rep z.gap pre ≤ 2*Clen*xi at hm
  have hwindow : representativeWindow rep z b₀ b₁ pre := by
    exact actual_mark_to_representative_window
      (r := (terminal w z pre).gap) (rrep := representativeGap rep z.gap pre)
      (x := (terminal w z pre).cutoff) (xrep := rep (pre.getLastD 0))
      (Delta := 2*Clen*xi) (h := xi/Real.log w) hb₀ hwin.2.2.2.1 hwin.2.2.2.2.1
      (by linarith [hxerr.1]) (by linarith [hxerr.2]) (by linarith [hm.1]) (by linarith [hm.2])
      (by rw [hratio]; exact hwin.2.1) (by rw [hratio]; exact hwin.2.2.1) hh hsmall
  exact ⟨hwin.1,hne,hlenPre,source_list_boxed (zero_lt_one.trans hw) htop hxi pre hsourcePre,
    hsafePre,hwindow,t,htagPre,hcountPre,halignPre⟩
end NumberTheoryLean.MarkedPrefixCandidate

end

section

namespace NumberTheoryLean.SourceMarkedStopping
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ActualSourceTags FiniteFirstTag MarkedPrefixTools SuccessfulMarkedCoordinates
open ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosInverseAlignment
open MarkedPrefixCandidate StoppedPrefixExistence StoppedCountAdapters StoppedVertexHistory
open StoppedEvaluation StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem marked_prefix_forces_actual_stop (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀)
    (hsearch : b₁ < w^((1/4:ℝ))) (hh : xi/Real.log w ≤ b₀)
    (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (a : ℕ → ℕ) (H : Finset ℕ) (mu : ℝ) (z : Node) (ps pre tail : List ℕ) (heq : ps=pre++tail)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (href : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hsafe : representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) ps)
    (t : Tag (binCount w top xi))
    (htag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t)
    (hcount : (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1)
    (halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p)
    (hwin : primeWindow b₀ b₁ (terminal w z pre)) :
    ∃ first rest : List ℕ,ps=first++rest ∧ first ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z H (sourcePrimeSet w top) mu) := by
  have hc := marked_prefix_candidate Y hw htop hxi hC hcomp hb₀ hCs hsearch hh hsmall
    a z ps pre tail heq hs hz hg hclosed hcap hroot href hlen hsafe t htag hcount halign hwin
  apply reference_candidate_forces_stop w _ (rootVertex z H (sourcePrimeSet w top) mu) ps href
  refine ⟨pre,tail,heq,?_⟩
  unfold lowerStop
  rw [after_node,after_past]
  simpa only [rootVertex,List.nil_append] using hc
end NumberTheoryLean.SourceMarkedStopping

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LargeGapCountErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.LiteralCountErrorLedger
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open FlatStoppedIdentity ReferenceAdmission ErdosInverseCounts StoppedTraceAdmission

attribute [local instance] Classical.propDecidable

theorem expanded_reference_subset (w : ℝ) (P : Finset ℕ) (z : Node) (V : ℝ) (stop : List ℕ → Prop) (n : ℕ) :
    expanded w stop n (rootVertex z ∅ P V) ⊆ referencePrefixes w P z.side z.gap := by
  intro ps hps
  exact trace_reference_member w stop n (rootVertex z ∅ P V) (Or.inl hps)
end NumberTheoryLean.LiteralCountErrorLedger



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualRegularAdmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualRegularAdmission
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SafeSubsetBoxGeometry ReferenceAdmission ActualSourceTags FiniteFirstTag
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem regular_word_reference {w top xi Clen B K : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi)) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) :
    ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  have han := regular_word_anchor hw htop hxi hC hcomp hsmall z ps hp
  have hh := anchored_choice_geometry hw htop hxi hC hcomp z _ han
    (wordSelection (label (zero_lt_one.trans hw) htop hxi) ps)
    (wordSelection_mem hw htop hxi ps hd.2)
  rw [wordSelection_recovers _ ps hd.1] at hh
  exact hh.1

theorem regular_tag_singleton {Y w top xi Clen B K Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ regularWords hw htop hxi Clen B K z) (a : ℕ → ℤ)
    (t : Tag (binCount w top xi))
    (ht : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a ps=some t) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1 := by
  obtain ⟨pre,p,tail,heq,_hidx,hbin,_hp,hsearch,_ho,_ha,_hn⟩ :=
    sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a ps ht
  have hmem : p ∈ ps := by rw [heq]; simp
  have hm : t.bin ∈ ps.map (label (zero_lt_one.trans hw) htop hxi) :=
    List.mem_map.mpr ⟨p,hmem,hbin.symm⟩
  have hpos := List.count_pos_iff.mpr hm
  rw [← hbin] at hsearch
  have hle := (Finset.mem_filter.mp hp).2.2.2.2 t.bin hsearch
  omega
end NumberTheoryLean.ActualRegularAdmission


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RegularStoppedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RegularStoppedEvent
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualRegularAdmission ActualPrefixClearance RegularBadTagWords SourceMarkedStopping
open StoppedTraceSets StoppedCountAdapters PriorPrimeWindow MissingWindowPrimeMass
open StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem uncaptured_subset_exceptions {w top xi Cs eta Clen B K b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi))
    (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀) (hsearch : b₁ < w^((1/4:ℝ)))
    (hh : xi/Real.log w ≤ b₀) (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (Y : ℕ) (a : ℕ → ℕ) (z : Node) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hg : StrongState z) (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) :
    uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q ⊆
      regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∪
        missingWindowPrefixes w 1 K b₀ b₁ z := by
  intro ps hp
  obtain ⟨hr,⟨q,hq,ha⟩,hnotstop⟩ := Finset.mem_filter.mp hp
  have href := regular_word_reference hw htop hxi hC hcomp hmesh z ps hr
  by_cases hwin : hasPrimeWindow w b₀ b₁ z ps
  · by_cases hcorrect : ∃ t,ActualSourceTags.sourceTag Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t ∧ t.rational=q
    · obtain ⟨t,ht,htq⟩ := hcorrect
      obtain ⟨pre,tail,heq,hwin⟩ := hwin
      have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
      have hreg := (Finset.mem_filter.mp hr).2
      have hsafe := clearance_supplies_safety hw htop hxi hC hcomp hmesh z ps hd.2 hreg.1 hreg.2.1
      have hcount := regular_tag_singleton hw htop hxi z ps hr (sourceClass a) t ht
      have halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p := by
        simpa only [htq] using ha
      exact False.elim (hnotstop (marked_prefix_forces_actual_stop Y hw htop hxi hC hcomp hb₀ hCs hsearch hh hsmall
        a ∅ 1 z ps pre tail heq hs hz hg hclosed hcap hroot href hreg.1 hsafe t ht hcount halign hwin))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr,q,hq,ha,hcorrect⟩)
  · have hu := (source_reference_transport hw htop z hs hz hg hclosed hcap ps href).1
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,(Finset.mem_filter.mp hr).2.2.2.1,hwin⟩)

end NumberTheoryLean.RegularStoppedEvent


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ExpandedHardCapture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RegularStoppedMass
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualRegularAdmission ActualPrefixClearance RegularBadTagWords SourceMarkedStopping
open StoppedTraceSets StoppedCountAdapters PriorPrimeWindow MissingWindowPrimeMass
open StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment
open RegularStoppedEvent

attribute [local instance] Classical.propDecidable

theorem uncaptured_mass_le_exceptions {w top xi Cs eta Clen B K b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi))
    (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀) (hsearch : b₁ < w^((1/4:ℝ)))
    (hh : xi/Real.log w ≤ b₀) (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (Y : ℕ) (a : ℕ → ℕ) (z : Node) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hg : StrongState z) (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) :
    (∑ ps ∈ uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q,prefixWeight ps) ≤
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a),prefixWeight ps) +
      (∑ ps ∈ missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) := by
  have hsub := uncaptured_subset_exceptions (eta := eta) (K := K) hw htop hxi hC hcomp hmesh hb₀ hCs hsearch hh hsmall
    Y a z hs hz hg hclosed hcap hroot Q
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ps _ _ => prefixWeight_nonneg ps)).trans
  have he :
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∪
        missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) +
      (∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∩
        missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps) = _ := Finset.sum_union_inter
  have hn : 0 ≤ ∑ ps ∈ regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∩
    missingWindowPrefixes w 1 K b₀ b₁ z,prefixWeight ps := Finset.sum_nonneg (fun ps _ => prefixWeight_nonneg ps)
  linarith
end NumberTheoryLean.RegularStoppedMass



namespace NumberTheoryLean.StoppedGeometryInvariance
open FinitePathGeometry StoppedCountVertex StoppedCountAdapters StoppedEvaluation StoppedTraceSets
open RegularStoppedEvent SourceStopPredicate LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open LogarithmicBinPartition
open PrimeHistories

attribute [local instance] Classical.propDecidable

theorem traces_eq_of_geometry (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v v' : Vertex)
    (hn : v.node=v'.node) (hp : v.past=v'.past) (ha : v.available=v'.available) :
    traces w stop n v=traces w stop n v' := by
  induction n generalizing v v' with
  | zero =>
    simp only [traces]
    apply ite_cond_congr
    simp only [lowerStop,hn,hp]
  | succ n ih =>
    have hstop : lowerStop stop v ↔ lowerStop stop v' := by simp only [lowerStop,hn,hp]
    have hinc : includedPrimes w v=includedPrimes w v' := by simp only [includedPrimes,hn,ha]
    have hchild : ∀ p,traces w stop n (child w v p)=traces w stop n (child w v' p) := by
      intro p
      exact ih (child w v p) (child w v' p) (by simp only [child,hn])
        (by simp only [child,hp]) (by simp only [child,ha])
    simp only [traces,hstop,hinc,hchild]

theorem root_stopped_independent (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (z : Node)
    (P H H' : Finset ℕ) (mu mu' : ℝ) :
    stopped w stop n (rootVertex z H P mu)=stopped w stop n (rootVertex z H' P mu') :=
  congrArg Prod.snd (traces_eq_of_geometry w stop n _ _ rfl rfl rfl)

theorem hasSourceStop_iff_original_root {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (H : Finset ℕ) (mu : ℝ) :
    hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps ↔
      ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w
        (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
          (label (zero_lt_one.trans hw) htop hxi) a z)
        (sourcePrimeSet w top).card (rootVertex z H (sourcePrimeSet w top) mu) := by
  unfold hasSourceStop
  rw [root_stopped_independent w _ _ z (sourcePrimeSet w top) ∅ H 1 mu]
end NumberTheoryLean.StoppedGeometryInvariance



namespace NumberTheoryLean.ExpandedNoStop
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets FirstStopSemantics
open FinitePathGeometry StoppedCountAdapters RegularStoppedEvent StoppedGeometryInvariance
open SourceStopPredicate LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem expanded_no_lower_stop (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v) :
    ∀ pre tail : List ℕ,ps=pre++tail → ¬lowerStop stop (after w v pre) := by
  induction n generalizing v ps with
  | zero =>
    unfold expanded at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · exact False.elim (Finset.notMem_empty _ hp)
    · have he : ps=[] := Finset.mem_singleton.mp hp
      subst ps
      intro pre tail heq
      have hpre := (List.append_eq_nil_iff.mp heq.symm).1
      simpa only [hpre,after] using hs
  | succ n ih =>
    unfold expanded at hp
    rw [traces] at hp
    split_ifs at hp with hs
    · exact False.elim (Finset.notMem_empty _ hp)
    · rcases Finset.mem_insert.mp hp with he | hp
      · subst ps
        intro pre tail heq
        have hpre := (List.append_eq_nil_iff.mp heq.symm).1
        simpa only [hpre,after] using hs
      · obtain ⟨p,_hinc,hps⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨qs,hqs,rfl⟩ := Finset.mem_image.mp hps
        intro pre tail heq
        cases pre with
        | nil => exact hs
        | cons q pre =>
          rw [List.cons_append] at heq
          obtain ⟨he,htail⟩ := List.cons.inj heq
          subst q
          exact ih (child w v p) hqs pre tail htail

theorem expanded_no_stopped_prefix (w : ℝ) (stop : List ℕ → Prop) (n N : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v) :
    ¬∃ pre tail : List ℕ,ps=pre++tail ∧ pre∈stopped w stop N v := by
  rintro ⟨pre,tail,he,hstop⟩
  exact expanded_no_lower_stop w stop n v hp pre tail he (stopped_first w stop N v hstop).1

theorem expanded_no_source_stop {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ) {ps : List ℕ}
    (hp : ps∈expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu)) :
    ¬hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps := by
  rw [hasSourceStop_iff_original_root hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps H mu]
  exact expanded_no_stopped_prefix w _ n _ _ hp
end NumberTheoryLean.ExpandedNoStop



namespace NumberTheoryLean.PaperRegularStopping
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate SourceNodeCoordinates
open JacobsthalSourceScale PaperMissingPrimeWindow ActualRegularBoxes ActualPrefixClearance
open RegularStoppedEvent RegularStoppedMass PaperRegularTagCapture MovingStopMargins
open ActualBinOwners StrongReferenceTransport LogarithmicBinScale

attribute [local instance] Classical.propDecidable

theorem paper_regular_uncaptured_mass {R Clen Cs eta xi : ℝ} (hR : 3 ≤ R) (hC : 1 ≤ Clen) (hCs : 0 ≤ Cs)
    (heta0 : 0 < eta) (heta : eta < 1/2) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hDelta : 2*Clen*xi ≤ 1) (H : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ,10 < rho ∧ ∀ K : ℝ,0 < K →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℕ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ Q : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) R z,(Q mult).card ≤ H) →
      (∀ mult ∈ regularBoxes hw htop hxi Clen (sourceB (Real.log top)) R z,
        ∀ q ∈ Q mult,eligible Y (sourceW (Real.log top)) Cs q) →
      (sourceB (Real.log top))^2 *
        (∑ ps ∈ uncapturedRegular hw htop hxi Y Cs eta Clen (sourceB (Real.log top)) R
          (K*(Real.log (sourceW (Real.log top)))^2)
          (rho*K*(Real.log (sourceW (Real.log top)))^2) a z Q,
          ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ epsilon := by
  obtain ⟨rho,hrho,hK⟩ := paper_missing_prime_window_mass_jb247 R (epsilon/2) hR (by positivity)
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨L₀,_hL₀,hmiss⟩ := hK K hKpos
  have hwT := sourceW_tendsto.comp Real.tendsto_log_atTop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [paper_regular_bad_tag_mass_jb247 hR hC hCs heta0 heta hxi hxi1 hDelta H (epsilon/2) (by positivity),
    hwT.eventually (moving_stop_margins Cs Clen xi hxi (by linarith : 0 < rho) hKpos),
    Real.tendsto_log_atTop.eventually source_scale_eventually,
    Real.tendsto_log_atTop.eventually sourceW_le_sourceB_eventually,
    hBT.eventually_ge_atTop 3,Real.tendsto_log_atTop.eventually_ge_atTop L₀,
    eventually_gt_atTop (1:ℝ)] with top htag hmargin hscale hWB hB3 hL htop1
  obtain ⟨hw,htop,htag⟩ := htag
  obtain ⟨_hw,hlog,hb₀,hCsWin,hsearch,hh,hsmall,hbelow⟩ := hmargin
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed Q hcard helig
  have hs := (source_node_bounds hscale.2.1 z hi h199 h23 hz hcut).1
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : (sourceW (Real.log top))^z.cutoff=top := by
    rw [hcut]
    exact (sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop1))
  have hroot : (rho*K*(Real.log (sourceW (Real.log top)))^2)/2 < z.cutoff := by
    rw [hcut]
    exact hbelow _ hWB
  have hm := uncaptured_mass_le_exceptions (eta := eta) (K := R) hw htop hxi (by linarith : 0 ≤ Clen) hscale.2.2.2.2
    (source_mesh_clearance_condition hlog hxi.le hC) hb₀ hCsWin hsearch hh hsmall
    Y a z hs hz hg hclosed hcap hroot Q
  have htagmass := htag Y hY z (sourceClass a) hi h199 h23 hz hcut hclosed Q hcard helig
  have hmissmass := hmiss (Real.log top) hL 1 (by norm_num) (by norm_num) z hi h199 h23 hz hcut
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg (sourceB (Real.log top)))
  rw [mul_add] at hm'
  simp only [Function.comp_def] at hm'
  linarith
end NumberTheoryLean.PaperRegularStopping



namespace NumberTheoryLean.ExpandedHardCapture
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualRegularBoxes ActualWordSelection
open StoppedCountAdapters StoppedTraceSets RegularStoppedEvent ExpandedNoStop
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem expanded_listed_subset_uncaptured {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu))
    (hreg : F ⊆ regularWords hw htop hxi Clen B K z)
    (halign : ∀ ps∈F,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p) :
    F ⊆ uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q := by
  intro ps hp
  exact Finset.mem_filter.mpr ⟨hreg hp,halign ps hp,
    expanded_no_source_stop hw htop hxi Y Cs eta Clen B b₀ b₁ a z H mu n (hexp hp)⟩

theorem expanded_listed_mass_le {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu))
    (hreg : F ⊆ regularWords hw htop hxi Clen B K z)
    (halign : ∀ ps∈F,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p) :
    (∑ ps∈F,prefixWeight ps) ≤
      ∑ ps∈uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q,prefixWeight ps :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (expanded_listed_subset_uncaptured hw htop hxi Y Cs eta Clen B K b₀ b₁ a z H mu n Q F hexp hreg halign)
    (fun ps _ _ => prefixWeight_nonneg ps)
end NumberTheoryLean.ExpandedHardCapture


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_PaperGeometricRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ExpandedCompactPartition
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualRegularBoxes ActualWordSelection
open StoppedCountAdapters StoppedTraceSets ExpandedHardCapture RegularStoppedEvent
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open GeometricRegularWords CountErrorClassification LiteralCountErrorLedger
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem expanded_geometric_mass_split {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta C B K L alpha beta b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (H : Finset ℕ) (mu : ℝ) (n : ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ))
    (hexp : F ⊆ expanded w
      (stopCandidate Y w Cs eta C B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu)) :
    (∑ ps∈F,prefixWeight ps) ≤
      (∑ ps∈F\geometricWords hw htop hxi C B K L alpha beta z,prefixWeight ps)+
      (∑ ps∈unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F,prefixWeight ps)+
      ∑ ps∈uncapturedRegular hw htop hxi Y Cs eta C B K b₀ b₁ a z Q,prefixWeight ps := by
  let G := geometricWords hw htop hxi C B K L alpha beta z
  let T := (F∩G).filter (listedWord hw htop hxi Cs a Q)
  have hTexp : T ⊆ expanded w
      (stopCandidate Y w Cs eta C B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      n (rootVertex z H (sourcePrimeSet w top) mu) :=
    fun _ hp => hexp (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).1
  have hTreg : T ⊆ regularWords hw htop hxi C B K z :=
    fun _ hp => (Finset.mem_filter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).2).1
  have hTalign : ∀ ps∈T,∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hbound := expanded_listed_mass_le hw htop hxi Y Cs eta C B K b₀ b₁ a z H mu n Q T hTexp hTreg hTalign
  have hsplit := Finset.sum_filter_add_sum_filter_not (F∩G) (listedWord hw htop hxi Cs a Q) prefixWeight
  have hgeo := Finset.sum_filter_add_sum_filter_not F (fun ps => ps∈G) prefixWeight
  simp only [Finset.filter_mem_eq_inter,← Finset.sdiff_eq_filter] at hgeo
  change (∑ ps∈F,prefixWeight ps) ≤ (∑ ps∈F\G,prefixWeight ps)+
    (∑ ps∈(F∩G).filter (fun ps => ¬listedWord hw htop hxi Cs a Q ps),prefixWeight ps)+_
  dsimp only [T] at hbound
  linarith

theorem bad_compact_reference_data (w top K eps : ℝ) (Y : ℕ) (a : ℕ → ℕ)
    (z : Node) (stop : List ℕ → Prop) (n : ℕ) (V0 : ℝ) :
    let F := badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a V0 z
      (expanded w stop n (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0)))
    F ⊆ ReferenceAdmission.referencePrefixes w (sourcePrimeSet w top) z.side z.gap ∧
      ∀ ps∈F,(terminal w z ps).gap ≤ K := by
  dsimp only
  exact ⟨fun _ hp => expanded_reference_subset w _ z _ stop n (Finset.mem_filter.mp hp).1,
    fun _ hp => (Finset.mem_filter.mp hp).2.1⟩
end NumberTheoryLean.ExpandedCompactPartition



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EligibleBoxLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.EligibleBoxLists
open ActualBinOwners LogarithmicBinScale

attribute [local instance] Classical.propDecidable

theorem mem_eligibleLists {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (m : Fin n → ℕ) (q : ℚ) :
    q∈eligibleLists Y w Cs M Q m ↔ m∈M ∧ q∈Q m ∧ eligible Y w Cs q := by
  by_cases hm : m∈M <;> simp [eligibleLists,hm]

theorem eligibleLists_card {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (NQ : ℕ) (hQ : ∀ m∈M,(Q m).card ≤ NQ) :
    ∀ m,(eligibleLists Y w Cs M Q m).card ≤ NQ := by
  intro m
  by_cases hm : m∈M
  · simpa only [eligibleLists,ite_eq_left hm] using (Finset.card_filter_le (Q m) _).trans (hQ m hm)
  · simp [eligibleLists,hm]

theorem eligibleLists_eligible {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) :
    ∀ m,∀ q∈eligibleLists Y w Cs M Q m,eligible Y w Cs q := by
  intro m q hq
  exact ((mem_eligibleLists Y w Cs M Q m q).mp hq).2.2

end NumberTheoryLean.EligibleBoxLists


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_OutsideExceptionsWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FilteredBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord FiniteBoxWordMass
open ErdosPrimeInputs.PrimePrefixMass
open GeometricBoxImages ExpandedCompactPartition GeometricRegularWords ActualWordSelection
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem filtered_word_box_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (F : Finset (List ℕ)) :
    (∑ ps∈(wordBox P m).filter (fun ps => ps∈F),prefixWeight ps)=selectedWordMass P m F := by
  have he : (wordBox P m).filter (fun ps => ps∈F)=
      ((selections P m).filter (fun f => descendingWord f∈F)).image descendingWord := by
    ext ps
    simp only [wordBox,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hF⟩
      exact ⟨f,⟨hf,hF⟩,rfl⟩
    · rintro ⟨f,⟨hf,hF⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,hF⟩
  rw [he,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    rw [StoppedVertexHistory.prefixWeight_product,
      descendingWord_product P hd f (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hf).1 k).1)]
  · intro f hf g hg heq
    exact word_injective P hd f g
      (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hf).1 k).1)
      (fun k => ((mem_selections _ _ _).mp (Finset.mem_filter.mp hg).1 k).1) heq

theorem filtered_box_mass {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (M : Finset (Fin n → ℕ)) (F : Finset (List ℕ)) (hF : F ⊆ boxWords P M) :
    (∑ ps∈F,prefixWeight ps)=∑ m∈M,selectedWordMass P m F := by
  have he : F=M.biUnion (fun m => (wordBox P m).filter (fun ps => ps∈F)) := by
    ext ps
    constructor
    · intro hp
      obtain ⟨m,hm,hps⟩ := Finset.mem_biUnion.mp (hF hp)
      exact Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_filter.mpr ⟨hps,hp⟩⟩
    · intro hp
      obtain ⟨_m,_hm,hps⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp hps).2
  calc
    _ = ∑ ps∈M.biUnion (fun m => (wordBox P m).filter (fun ps => ps∈F)),prefixWeight ps := by rw [← he]
    _ = ∑ m∈M,∑ ps∈(wordBox P m).filter (fun ps => ps∈F),prefixWeight ps := by
      apply Finset.sum_biUnion
      intro m _hm m' _hm' hne
      exact (wordBoxes_disjoint P hd m m' hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    _ = _ := Finset.sum_congr rfl (fun m _ => filtered_word_box_mass P m hd F)

theorem unlisted_geometric_box_mass {w top xi Cs C B K L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (F : Finset (List ℕ)) :
    let U := unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F
    (∑ ps∈U,prefixWeight ps)=∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,
      selectedWordMass (globalBins w top xi) m U := by
  dsimp only
  apply filtered_box_mass _ (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
  intro ps hp
  have hg := (Finset.mem_inter.mp (Finset.mem_filter.mp hp).1).2
  have hr := (Finset.mem_filter.mp hg).1
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
  apply Finset.mem_biUnion.mpr
  refine ⟨wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps,
    Finset.mem_image.mpr ⟨ps,hg,rfl⟩,?_⟩
  exact Finset.mem_image.mpr ⟨wordSelection (label (zero_lt_one.trans hw) htop hxi) ps,
    wordSelection_mem hw htop hxi ps hd.2,wordSelection_recovers _ ps hd.1⟩
end NumberTheoryLean.FilteredBoxWordMass



namespace NumberTheoryLean.SoftWitnessCapture
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ActualWordSelection FiniteBoxWordMass EligibleBoxLists
open ExpandedCompactPartition ActualBinOwners SingletonBinSelection TwoPrimeObservableSum
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem word_selection_descending {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) :
    wordSelection (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=f := by
  have hrec := wordSelection_mem hw htop hxi (descendingWord f) (word_source_membership hw htop hxi m f hf)
  apply word_injective (globalBins w top xi)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    _ f (fun k => ((mem_selections _ _ _).mp hrec k).1) (fun k => ((mem_selections _ _ _).mp hf k).1)
  exact wordSelection_recovers _ _ (descendingWord_strict f)

theorem word_multiplicity_descending {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) :
    wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=m := by
  funext k
  unfold wordMultiplicity
  rw [word_selection_descending hw htop hxi m f hf]
  exact ((mem_selections _ _ _).mp hf k).2

end NumberTheoryLean.SoftWitnessCapture



namespace NumberTheoryLean.EligibleListWord
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ActualWordSelection SoftWitnessCapture EligibleBoxLists ExpandedCompactPartition ActualBinOwners
open LogarithmicBinScale LogarithmicBinLabels
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem listed_word_eligible_iff {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℕ) (ps : List ℕ) :
    listedWord hw htop hxi Cs a (eligibleLists Y w Cs M Q) ps ↔
      wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps∈M ∧
      ∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),eligible Y w Cs q ∧
        ∀ p∈ps,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  unfold listedWord
  constructor
  · rintro ⟨q,hq,ha⟩
    obtain ⟨hm,hq,he⟩ := (mem_eligibleLists _ _ _ _ _ _ _).mp hq
    exact ⟨hm,q,hq,he,ha⟩
  · rintro ⟨hm,q,hq,he,ha⟩
    exact ⟨q,(mem_eligibleLists _ _ _ _ _ _ _).mpr ⟨hm,hq,he⟩,ha⟩

theorem listed_selection_eligible_iff {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℝ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (a : ℕ → ℕ) :
    listedWord hw htop hxi Cs a (eligibleLists Y w Cs M Q) (descendingWord f) ↔
      ∃ q∈Q m,eligible Y w Cs q ∧
        ∀ p∈descendingWord f,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  rw [listed_word_eligible_iff hw htop hxi Y M Q a,word_multiplicity_descending hw htop hxi m f hf]
  exact and_iff_right hm

theorem unlisted_compact_selected_data {w top xi Cs C B K L alpha beta eps : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (F : Finset (List ℕ))
    (hu : descendingWord f∈unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q)
      (CountErrorClassification.badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
        (SmallSieveFinite.smallEuler ⌊w⌋₊) z F)) :
    descendingWord f∈GeometricRegularWords.geometricWords hw htop hxi C B K L alpha beta z ∧
      eps < |ActualCountErrorEdges.wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
        (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| ∧
      ¬∃ q∈Q m,eligible Y w Cs q ∧
        ∀ p∈descendingWord f,Cs < primeExponent w p → aligns (SourceStopPredicate.sourceClass a) q p := by
  obtain ⟨hmem,hnot⟩ := Finset.mem_filter.mp hu
  have hh := Finset.mem_inter.mp hmem
  refine ⟨hh.2,(Finset.mem_filter.mp hh.1).2.2,?_⟩
  exact fun hwit => hnot ((listed_selection_eligible_iff hw htop hxi Y M Q m hm f hf a).mpr hwit)
end NumberTheoryLean.EligibleListWord



open _root_.Filter


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
open FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages SafeSubsetBoxGeometry CanonicalSubsetBox FilteredBoxWordMass
open LogarithmicBinScale ErdosSubsetWord


theorem unlisted_box_transfer {w top xi Cs C B K L alpha beta sigma A : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hsigma : 0 ≤ sigma)
    (a : ℕ → ℕ) (z : Node) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (F : Finset (List ℕ))
    (hTotal : B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,selectionMass (globalBins w top xi) m) ≤ A)
    (hBox : ∀ m∈geometricBoxes hw htop hxi C B K L alpha beta z,
      selectedWordMass (globalBins w top xi) m
        (ExpandedCompactPartition.unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F)
        ≤ sigma*selectionMass (globalBins w top xi) m) :
    B^2*(∑ ps∈ExpandedCompactPartition.unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F,
      ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ sigma*A := by
  rw [unlisted_geometric_box_mass hw htop hxi a z Q F]
  calc
    _ ≤ B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,sigma*selectionMass (globalBins w top xi) m) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBox) (sq_nonneg B)
    _ = sigma*(B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,selectionMass (globalBins w top xi) m)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTotal hsigma
end NumberTheoryLean.GeometricTotalBoxMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualUnlistedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualUnlistedEvent
open ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible
open EligibleBoxLists ExpandedCompactPartition FilteredBoxWordMass
open LogarithmicBinScale
attribute [local instance] Classical.propDecidable

theorem selected_unlisted_le_unwitnessed_mass {w top xi Cs C B K L alpha beta eps : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (M : Finset (Fin (binCount w top xi) → ℕ))
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (m : Fin (binCount w top xi) → ℕ) (hm : m∈M)
    (a : ℕ → ℕ) (z : PrimeHistories.Node) (F : Finset (List ℕ)) :
    selectedWordMass (globalBins w top xi) m
      (unlistedGeometric hw htop hxi Cs C B K L alpha beta a z (eligibleLists Y w Cs M Q)
        (CountErrorClassification.badCompactWords w K eps Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a
          (SmallSieveFinite.smallEuler ⌊w⌋₊) z F)) ≤
      ∑ f∈(selections (globalBins w top xi) m).filter
        (unwitnessedSelection hw htop hxi Y Cs C B K L alpha beta eps a z (Q m)),
        (selectionProduct f:ℝ)⁻¹ := by
  simp only [selectedWordMass,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro f hf
  split_ifs with hU hActual hActual
  · exact le_rfl
  · apply False.elim
    apply hActual
    exact EligibleListWord.unlisted_compact_selected_data hw htop hxi Y M Q m hm f hf a z F hU
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl
end NumberTheoryLean.ActualUnlistedEvent


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SourceCompactErrorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GlobalCompactTransfer
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open JacobsthalSourceScale ActualRegularBoxes ActualBinOwners UniformGeometricRegularMass
open GeometricTotalBoxMass GeometricBoxImages GeometricRegularWords
open ExpandedCompactPartition CountErrorClassification RegularStoppedEvent PaperRegularStopping
open EligibleBoxLists ActualUnlistedEvent FilteredBoxWordMass CanonicalSubsetBox
open StoppedCountVertex StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem paper_compact_from_local_bounds (K : ℝ) (hK : 3 ≤ K) :
    ∃ Clen₀ Cgeom A : ℝ,1 ≤ Clen₀ ∧ 0 < Cgeom ∧ 0 < A ∧
    ∀ Clen : ℝ,Clen₀ ≤ Clen → ∀ geoErr : ℝ,0 < geoErr →
    ∃ alpha : ℝ,0 < alpha ∧ alpha ≤ 1/400 ∧
    ∀ L Cs eta : ℝ,0 ≤ L → 0 ≤ Cs → 0 < eta → eta < 1/2 →
    ∀ NQ : ℕ,∀ capErr : ℝ,0 < capErr → ∀ xi : ℝ,∀ hxi : 0 < xi,
      xi ≤ 1 → 20*Clen*xi ≤ 1 →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ Y : ℕ,Y ≤ ⌊top^2/(Real.log top)^2⌋₊ → ∀ (z : Node) (a : ℕ → ℕ),
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z →
      z.cutoff=sourceB (Real.log top) → z.closed=true →
      ∀ eps tau : ℝ,0 ≤ tau →
      ∀ Qraw : (Fin (binCount (sourceW (Real.log top)) top xi) → ℕ) → Finset ℚ,
      let M := geometricBoxes hw htop hxi Clen (sourceB (Real.log top)) K L alpha (1/100) z
      (∀ m∈M,(Qraw m).card ≤ NQ) →
      (∀ m∈M,(∑ f∈(selections (globalBins (sourceW (Real.log top)) top xi) m).filter
        (unwitnessedSelection hw htop hxi Y Cs Clen (sourceB (Real.log top)) K L alpha (1/100) eps a z (Qraw m)),
        (selectionProduct f:ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW (Real.log top)) top xi) m) →
      let w := sourceW (Real.log top)
      let B := sourceB (Real.log top)
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      B^2*(∑ ps∈badCompactWords w K eps Y small a V0 z
        (expanded w stop (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0))),prefixWeight ps)
        ≤ Cgeom*(2*Clen*xi)+geoErr+A*tau+capErr := by
  obtain ⟨A,BA,WA,hA,hBA,hWA,hTotal⟩ := uniform_geometric_box_mass_jb247 K hK
  obtain ⟨Clen₀,Cgeom,hClen₀,hCgeom,hGeometry⟩ := geometric_defect_uniform_in_L_jb247 K hK 2 (by norm_num)
    (1/400) (by norm_num) (by norm_num)
  refine ⟨Clen₀,Cgeom,A,hClen₀,hCgeom,hA,?_⟩
  intro Clen hClen geoErr hgeoErr
  have hClen1 : 1 ≤ Clen := hClen₀.trans hClen
  obtain ⟨alpha,halpha,halphaUpper,hL⟩ := hGeometry Clen hClen geoErr hgeoErr
  refine ⟨alpha,halpha,halphaUpper,?_⟩
  intro L Cs eta hL0 hCs heta0 heta NQ capErr hcapErr xi hxi hxi1 h20
  obtain ⟨BG,WG,hBG,hWG,hGeometry⟩ := hL L hL0
  have hbeta : 4*(1/400:ℝ)=1/100 := by norm_num
  rw [hbeta] at hGeometry
  have hDelta : 2*Clen*xi ≤ 1 := by
    have hp : 0 ≤ Clen*xi := mul_nonneg (by linarith) hxi.le
    nlinarith
  obtain ⟨rho,hrho,hCapture⟩ := paper_regular_uncaptured_mass hK hClen1 hCs heta0 heta hxi hxi1 hDelta NQ capErr hcapErr
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  have hBT := sourceB_tendsto.comp Real.tendsto_log_atTop
  have hWT := sourceW_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hCapture Kstop hKstop,hBT.eventually_ge_atTop (max BG BA),
    hWT.eventually_ge_atTop (max WG WA),Real.tendsto_log_atTop.eventually source_scale_eventually]
    with top hCapture hB hW hscale
  dsimp only [Function.comp_def] at hB hW
  obtain ⟨hw,htop,hCapture⟩ := hCapture
  refine ⟨hw,htop,?_⟩
  intro Y hY z a hi h199 h23 hz hcut hclosed eps tau htau Qraw
  dsimp only
  intro hcard hLocal
  let w := sourceW (Real.log top)
  let B := sourceB (Real.log top)
  let P := sourcePrimeSet w top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  let M := geometricBoxes hw htop hxi Clen B K L alpha (1/100) z
  let Q := eligibleLists (Y:ℝ) w Cs M Qraw
  let b₀ := Kstop*(Real.log w)^2
  let b₁ := rho*Kstop*(Real.log w)^2
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z
  let F := badCompactWords w K eps Y small a V0 z (expanded w stop P.card v)
  have hpower : w^B=top := (sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  have hRef := bad_compact_reference_data w top K eps Y a z stop P.card V0
  have hGeom := hGeometry B w top ((le_max_left _ _).trans hB) ((le_max_left _ _).trans hW)
    hw htop xi hxi hxi1 h20 hscale.2.2.2.2 z hi h199 h23 hz hcut hclosed hpower F hRef.1 hRef.2
  have hTot := hTotal B w top ((le_max_right _ _).trans hB) ((le_max_right _ _).trans hW)
    hw htop xi Clen hxi hClen1 hscale.2.2.2.2 hDelta z hi h199 h23 hz hcut hclosed hpower L alpha (1/100)
  have hCard := eligibleLists_card (Y:ℝ) w Cs M Qraw NQ hcard
  have hCap := hCapture Y hY z a hi h199 h23 hz hcut hclosed Q
    (fun m _hm => hCard m) (fun m _hm q hq => eligibleLists_eligible (Y:ℝ) w Cs M Qraw m q hq)
  have hBox : ∀ m∈M,selectedWordMass (globalBins w top xi) m
      (unlistedGeometric hw htop hxi Cs Clen B K L alpha (1/100) a z Q F) ≤ tau*selectionMass (globalBins w top xi) m := by
    intro m hm
    exact (selected_unlisted_le_unwitnessed_mass (Cs:=Cs) (C:=Clen) (B:=B) (K:=K) (L:=L)
      (alpha:=alpha) (beta:=1/100) (eps:=eps) hw htop hxi Y M Qraw m hm a z (expanded w stop P.card v)).trans (hLocal m hm)
  have hUnlisted := unlisted_box_transfer hw htop hxi htau a z Q F hTot hBox
  have hSplit := expanded_geometric_mass_split hw htop hxi Y Cs eta Clen B K L alpha (1/100) b₀ b₁ a z
    ∅ ((Y:ℝ)*V0) P.card Q F (fun _ hp => (Finset.mem_filter.mp hp).1)
  have hScaled := mul_le_mul_of_nonneg_left hSplit (sq_nonneg B)
  change B^2*(∑ ps∈F,prefixWeight ps) ≤ Cgeom*(2*Clen*xi)+geoErr+A*tau+capErr
  nlinarith
end NumberTheoryLean.GlobalCompactTransfer



namespace NumberTheoryLean.SourceCompactErrorMass
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open GlobalCompactTransfer GeometricBoxImages GeometricRegularWords CountErrorClassification
open StoppedCountVertex StoppedCountAdapters StoppedTraceSets CanonicalSubsetBox
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInverseBoxHeight ErdosCofactorChoices ErdosSubsetWord ErdosVarianceEligible ErdosVarianceFactory
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem source_compact_error_mass_jb247_oai (K eps budget aStar Cmin : ℝ)
    (hK : 3 ≤ K) (heps : 0 < eps) (hbudget : 0 < budget) (ha : 0 < aStar) (ha1 : aStar ≤ 1) :
    ∃ Clen Cs xi₀ : ℝ,1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ eta : ℝ,0 < eta → eta < 1/2 → ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ (z : Node) (a : ℕ → ℕ),z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
        Consistent z → z.cutoff=sourceB top → z.closed=true →
        z.gap=Real.log (sourceY top:ℝ)/Real.log (sourceW top)-aStar+2 →
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      B^2*(∑ ps∈badCompactWords w K eps Y small a V0 z
        (expanded w stop (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*V0))),prefixWeight ps) ≤ budget := by
  obtain ⟨Clen,Cgeom,A,hClen,hCgeom,hA,hGlobal⟩ := paper_compact_from_local_bounds K hK
  have hClen0 : 0 < Clen := by linarith
  have hquarter : 0 < budget/4 := by positivity
  obtain ⟨alpha,halpha,_halphaUpper,hGlobal⟩ := hGlobal Clen (le_refl _) (budget/4) hquarter
  let tau := budget/(4*A)
  have htau : 0 < tau := by dsimp [tau] <;> positivity
  obtain ⟨Kstar,hKstar,NQ,Cs,hCs,hCsMin,_hCsK,xiF,hxiF,hxiF1,hFactory⟩ :=
    source_raw_box_factory_jb247 Clen K aStar alpha eps tau Cmin hClen hK ha ha1 halpha heps htau
  let xi₀ := min xiF (min (1/(20*Clen)) (budget/(8*Clen*Cgeom)))
  have hxi₀ : 0 < xi₀ := lt_min hxiF (lt_min (by positivity) (by positivity))
  have hxi₀1 : xi₀ ≤ 1 := (min_le_left _ _).trans hxiF1
  refine ⟨Clen,Cs,xi₀,hClen,hCs,hCsMin,hxi₀,hxi₀1,?_⟩
  intro eta heta0 heta xi hxi hx
  have hxF : xi ≤ xiF := hx.trans (min_le_left _ _)
  have hxi1 : xi ≤ 1 := hx.trans hxi₀1
  have h20 : 20*Clen*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 20*Clen by positivity)).mp
      ((hx.trans (min_le_right _ _)).trans (min_le_left _ _))
    nlinarith
  have hGeomBudget : Cgeom*(2*Clen*xi) ≤ budget/4 := by
    have hh := (le_div_iff₀ (show 0 < 8*Clen*Cgeom by positivity)).mp
      ((hx.trans (min_le_right _ _)).trans (min_le_right _ _))
    nlinarith
  have hL : 0 ≤ 2*Kstar+5 := by linarith
  obtain ⟨rho,hrho,hGlobal⟩ := hGlobal (2*Kstar+5) Cs eta hL hCs.le heta0 heta NQ (budget/4) hquarter xi hxi hxi1 h20
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  filter_upwards [hGlobal Kstop hKstop,hFactory xi hxi hxF] with top hGlobal hFactory
  obtain ⟨hw,htop,hGlobal⟩ := hGlobal
  obtain ⟨_hwF,_htopF,hFactory⟩ := hFactory
  refine ⟨hw,htop,?_⟩
  intro z a hi h199 h23 hz hcut hclosed hroot
  dsimp only
  let M := geometricBoxes hw htop hxi Clen (sourceB top) K (2*Kstar+5) alpha (1/100) z
  have hLists (m : Fin (binCount (sourceW top) top xi) → ℕ) (hm : m∈M) :=
    hFactory z hi h199 hz hcut hclosed hroot a m hm
  have hAll : ∀ m : Fin (binCount (sourceW top) top xi) → ℕ,∃ Q : Finset ℚ,
      Q.card ≤ NQ ∧ (m∈M →
      (∑ f∈(selections (globalBins (sourceW top) top xi) m).filter
        (unwitnessedSelection hw htop hxi (sourceY top) Cs Clen (sourceB top) K (2*Kstar+5) alpha (1/100) eps a z Q),
        (selectionProduct f:ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m) := by
    intro m
    by_cases hm : m∈M
    · obtain ⟨Q,hcard,hMass⟩ := hLists m hm
      exact ⟨Q,hcard,fun _ => hMass⟩
    · exact ⟨∅,by simp,fun hm' => False.elim (hm hm')⟩
  choose Qraw hCard hLocal using hAll
  have hBound := hGlobal (sourceY top) (le_refl _) z a hi h199 h23 hz hcut hclosed eps tau htau.le Qraw
    (fun m _hm => hCard m) hLocal
  have hTau : A*tau=budget/4 := by dsimp [tau]; field_simp [hA.ne']
  rw [hTau] at hBound
  dsimp only at hBound
  exact hBound.trans (by nlinarith)
end NumberTheoryLean.SourceCompactErrorMass


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.SourceCompactErrorMass.source_compact_error_mass_jb247_oai := @OAI.Erdos970.NumberTheoryLean.SourceCompactErrorMass.source_compact_error_mass_jb247_oai
