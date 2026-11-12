-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Final.erdos_970_iterated_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:06.254193+00:00
-- url     : https://prove2.me/submissions/591bd9b2-6549-4d3f-b6a9-8c011b8c4524

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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
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
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG
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
import Definitions.Def_JacobsthalImproved
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_ErdosStoppedArithmetic_actual_owner_local_comparison_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_CanonicalKeyReference_moving_key_reference_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_IteratedLogBound_of_source_root_lower_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceRootErrorLower_source_root_lower_with_stopped_correction_jb247

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable
open _root_.Finset
open ReferencePruning ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.MertensStrong

theorem primeProduct_eq_survivor (x : ℝ) : primeProduct x=survivorProduct (Nat.primesLE ⌊x⌋₊) := by
  have he : (Ioc 0 ⌊x⌋₊).filter Nat.Prime=Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,hpx⟩,hp⟩
      exact ⟨hpx,hp⟩
    · rintro ⟨hpx,hp⟩
      exact ⟨⟨hp.pos,hpx⟩,hp⟩
  unfold primeProduct survivorProduct
  rw [he]
  simp only [one_div]

theorem prime_factor_pos {p : ℕ} (hp : p.Prime) : 0 < 1-(p:ℝ)⁻¹ := by
  apply sub_pos.mpr
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem actual_primeProduct_pos (x : ℝ) : 0 < primeProduct x := by
  rw [primeProduct_eq_survivor]
  exact Finset.prod_pos (fun p hp => prime_factor_pos (Nat.mem_primesLE.mp hp).2)

end NumberTheoryLean.ReferenceProductsBasics

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

theorem representative_safety_admits {r rrep x xrep Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hx : x ≤ xrep) (hr : rrep ≤ r)
    (hsafe : sourceHeight xrep+3*Delta ≤ rrep) : sourceHeight x ≤ r := by
  have hH := sourceHeight_mono hx
  linarith

theorem representative_to_actual_window {b₀ b₁ r rrep x xrep Delta h : ℝ}
    (hx : 0 < x) (hxr : x ≤ xrep) (hxh : xrep ≤ x+h)
    (hr : rrep ≤ r) (hrD : r ≤ rrep+Delta)
    (hb₀ : b₀ ≤ xrep) (hb₁ : xrep ≤ b₁)
    (hs₀ : 206/100 ≤ rrep/xrep) (hs₁ : rrep/xrep ≤ 216/100)
    (hsmall : Delta+(218/100)*h ≤ (2/100)*b₀) :
    b₀-h ≤ x ∧ x ≤ b₁ ∧ 204/100 ≤ r/x ∧ r/x ≤ 218/100 := by
  have hxp : 0 < xrep := hx.trans_le hxr
  have hlow := (le_div_iff₀ hxp).mp hs₀
  have hhigh := (div_le_iff₀ hxp).mp hs₁
  refine ⟨by linarith,hxr.trans hb₁,?_,?_⟩
  · apply (le_div_iff₀ hx).mpr
    nlinarith
  · apply (div_le_iff₀ hx).mpr
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

theorem firstTagFrom_append {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps qs : List ℕ)
    {t : Tag n} (ht : firstTagFrom F k ps = some t) : firstTagFrom F k (ps++qs) = some t := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom] at ht
  | cons p ps ih =>
    cases hp : F p with
    | none =>
      simp only [List.cons_append,firstTagFrom,hp] at ht ⊢
      exact ih (k+1) ht
    | some bq =>
      simpa only [List.cons_append,firstTagFrom,hp] using ht

theorem firstTagFrom_map_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (k : ℕ) (ps qs : List ℕ) (hmap : ps.map F = qs.map F) :
    firstTagFrom F k ps = firstTagFrom F k qs := by
  induction ps generalizing k qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hmap.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hmap
    | cons q qs =>
      have hh := List.cons.inj hmap
      simp only [firstTagFrom,hh.1]
      cases hq : F q with
      | none => exact ih (k+1) qs hh.2
      | some bq => rfl

theorem tag_replacement_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (pre tail : List ℕ) (p q : ℕ) (hpq : F p = F q) :
    firstTag F (pre++p::tail) = firstTag F (pre++q::tail) := by
  apply firstTagFrom_map_invariant
  simp only [List.map_append,List.map_cons,hpq]

theorem tag_prefix_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (ps qs : List ℕ) (hmap : ps.map F = qs.map F) (k : ℕ) :
    firstTag F (ps.take k) = firstTag F (qs.take k) := by
  apply firstTagFrom_map_invariant
  rw [List.map_take,List.map_take,hmap]

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

theorem candidate_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    tagCandidate Y w Cs eta lower width label a p' = tagCandidate Y w Cs eta lower width label a p := by
  have hc := candidate_witness Y w Cs eta lower width label a p ht
  have hs : searchBin w (lower (label p')) := by rw [hlabel]; exact hc.2.2.1
  have ho : owner Y w Cs eta (lower (label p')) (width (label p')) a = some q := by
    rw [hlabel]
    exact hc.2.2.2.1
  rw [candidate_of_witness Y w Cs eta lower width label a p' q hp' hs ho ha,ht,hlabel,← hc.1]

end NumberTheoryLean.ActualSourceTags

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

namespace ErdosInverseCounts
open NumberTheoryLean NumberTheoryLean.SievePartition

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

theorem candidate_admitted {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hw : 1 < w) (hC : 0 ≤ Clen) (hxi : 0 ≤ xi)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
    admitted w z.side z.gap ps := by
  apply finite_safe_admits w (representative w lower width label) z (2*Clen*xi) ps (by positivity)
  · intro p hp
    exact (bin_exponent_bounds hw (hlo (label p)) (hwidth (label p)) (hc.2.2.1 p hp)).2
  · exact hc.2.2.2.1

theorem candidate_owner_witness {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hw : 1 < w) (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
    ∃ t : Tag n,sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps = some t ∧
      (ps.map label).count t.bin = 1 ∧ eligible (Y:ℝ) w Cs t.rational ∧
      (1-eta)*((primeBin (lower t.bin) (width t.bin)).card:ℝ) ≤
        (((primeBin (lower t.bin) (width t.bin)).filter (aligns (sourceClass a) t.rational)).card:ℝ) ∧
      ∀ p ∈ ps,aligns (sourceClass a) t.rational p := by
  obtain ⟨t,ht,hm,ha⟩ := hc.2.2.2.2.2
  obtain ⟨_pre,_p,_tail,_hps,_hidx,hbin,_hp,_hsearch,ho,_hpa,_hbefore⟩ :=
    sourceTag_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) ps ht
  have hOwner := actual_owner_witness (Nat.cast_nonneg Y) hw (sourceClass a) ho
  rw [← hbin] at hOwner
  exact ⟨t,ht,hm,hOwner.1,hOwner.2,ha⟩

end NumberTheoryLean.SourceStopPredicate



namespace NumberTheoryLean.ActualTagFreezing

open ActualSourceTags FiniteFirstTag SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment

theorem sourceTag_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    sourceTag Y w Cs eta lower width label a (pre++p::tail) =
      sourceTag Y w Cs eta lower width label a (pre++p'::tail) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  exact tag_replacement_invariant _ pre tail p p' hc.symm

theorem all_prefix_tags_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') (k : ℕ) :
    sourceTag Y w Cs eta lower width label a ((pre++p::tail).take k) =
      sourceTag Y w Cs eta lower width label a ((pre++p'::tail).take k) := by
  have hc := candidate_replacement Y w Cs eta lower width label a p p' ht hlabel hp' ha
  apply tag_prefix_invariant
  simp only [List.map_append,List.map_cons,hc]

theorem replacement_labels {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ)
    (hlabel : label p' = label p) : (pre++p::tail).map label = (pre++p'::tail).map label := by
  simp only [List.map_append,List.map_cons,hlabel]

theorem replacement_representatives {n : ℕ} (w : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ) (hlabel : label p' = label p) :
    (pre++p::tail).map (representative w lower width label) =
      (pre++p'::tail).map (representative w lower width label) := by
  simp only [List.map_append,List.map_cons,representative,hlabel]

theorem forall_mem_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p q : ℕ)
    (hp : A p) (hq : A q) :
    (∀ r ∈ pre++p::tail,A r) ↔ (∀ r ∈ pre++q::tail,A r) := by
  have h (p q : ℕ) (hq : A q) (H : ∀ r ∈ pre++p::tail,A r) : ∀ r ∈ pre++q::tail,A r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact H r (List.mem_append.mpr (Or.inl hr))
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hq
      · exact H r (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hr)))
  exact ⟨h p q hq,h q p hp⟩

end NumberTheoryLean.ActualTagFreezing


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

theorem representativeWindow_map_iff (rep : ℕ → ℝ) (z : Node) (b₀ b₁ : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeWindow rep z b₀ b₁ ps ↔ representativeWindow rep z b₀ b₁ qs := by
  have he := representative_last_eq rep ps qs hm
  simp only [representativeWindow,representativeGap,he,hm]

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

theorem all_prefix_representative_tests (w : ℝ) (rep : ℕ → ℝ) (z : Node)
    (Delta b₀ b₁ : ℝ) (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) (k : ℕ) :
    (representativeSafe w rep z Delta (ps.take k) ↔ representativeSafe w rep z Delta (qs.take k)) ∧
    (representativeWindow rep z b₀ b₁ (ps.take k) ↔ representativeWindow rep z b₀ b₁ (qs.take k)) := by
  have ht : (ps.take k).map rep = (qs.take k).map rep := by rw [List.map_take,List.map_take,hm]
  exact ⟨representativeSafe_map_iff w rep z Delta _ _ ht,
    representativeWindow_map_iff rep z b₀ b₁ _ _ ht⟩
end NumberTheoryLean.RepresentativeTraceInvariance

end

section

namespace NumberTheoryLean.SourceCandidateFreezing
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate
open ActualSourceTags ActualTagFreezing FiniteFirstTag RepresentativeTraceInvariance
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem forall_take_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p p' : ℕ)
    (hp : A p) (hp' : A p') (k : ℕ) :
    (∀ r ∈ (pre++p::tail).take k,A r) ↔ (∀ r ∈ (pre++p'::tail).take k,A r) := by
  have hm : ((pre++p::tail).take k).map A = ((pre++p'::tail).take k).map A := by
    rw [List.map_take,List.map_take]
    have he : A p = A p' := propext (iff_of_true hp hp')
    simp only [List.map_append,List.map_cons,he]
  have forward (ps qs : List ℕ) (hm : ps.map A = qs.map A)
      (hh : ∀ r ∈ ps,A r) : ∀ r ∈ qs,A r := by
    intro r hr
    have hm' : A r ∈ ps.map A := by rw [hm]; exact List.mem_map.mpr ⟨r,hr,rfl⟩
    obtain ⟨s,hs,he⟩ := List.mem_map.mp hm'
    rw [← he]
    exact hh s hs
  exact ⟨forward _ _ hm,forward _ _ hm.symm⟩

theorem prefix_tag_eq {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ) (k : ℕ)
    {t u : Tag n} (ht : firstTag F ps = some t) (hu : firstTag F (ps.take k) = some u) : u=t := by
  have hh := firstTagFrom_append F 0 (ps.take k) (ps.drop k) hu
  rw [List.take_append_drop] at hh
  exact Option.some.inj (hh.symm.trans ht)

theorem all_prefix_candidate_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') (k : ℕ) :
    stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p::tail).take k) ↔
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p'::tail).take k) := by
  have hwit := candidate_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) p hc
  have hp := hwit.2.1
  have ha := hwit.2.2.2.2
  have htags := all_prefix_tags_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha' k
  have hfull := sourceTag_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha'
  have ht' : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p'::tail) = some t :=
    hfull.symm.trans ht
  have hlabels : ((pre++p::tail).take k).map label = ((pre++p'::tail).take k).map label := by
    rw [List.map_take,List.map_take,replacement_labels label pre tail p p' hlabel]
  have hrep := all_prefix_representative_tests w (representative w lower width label) z
    (2*Clen*xi) b₀ b₁ _ _ (replacement_representatives w lower width label pre tail p p' hlabel) k
  have hboxed := forall_take_replacement_iff
    (fun r => r ∈ primeBin (lower (label r)) (width (label r))) pre tail p p' hp hp' k
  have halign := forall_take_replacement_iff (aligns (sourceClass a) t.rational) pre tail p p' ha ha' k
  have hlen : ((pre++p::tail).take k).length = ((pre++p'::tail).take k).length := by
    simp only [List.length_take,List.length_append,List.length_cons]
  have hne : ((pre++p::tail).take k ≠ []) ↔ ((pre++p'::tail).take k ≠ []) := by
    rw [← List.length_pos_iff,← List.length_pos_iff,hlen]
  have forward (ps qs : List ℕ)
      (hps : firstTag (tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a))
        ((pre++p::tail).take k) = sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps)
      (htag : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps =
        sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) qs)
      (hne : ps ≠ [] → qs ≠ []) (hlen : ps.length = qs.length)
      (hb : boxed lower width label ps → boxed lower width label qs)
      (hs : representativeSafe w (representative w lower width label) z (2*Clen*xi) ps →
        representativeSafe w (representative w lower width label) z (2*Clen*xi) qs)
      (hw : representativeWindow (representative w lower width label) z b₀ b₁ ps →
        representativeWindow (representative w lower width label) z b₀ b₁ qs)
      (hl : ps.map label = qs.map label)
      (ha : (∀ r ∈ ps,aligns (sourceClass a) t.rational r) → ∀ r ∈ qs,aligns (sourceClass a) t.rational r)
      (H : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z qs := by
    obtain ⟨hn,hlength,hbox,hsafe,hwindow,u,hu,hcount,hal⟩ := H
    have hu' := hps.trans hu
    have hut : u=t := prefix_tag_eq _ (pre++p::tail) k ht hu'
    subst u
    exact ⟨hne hn,by simpa only [← hlen] using hlength,hb hbox,hs hsafe,hw hwindow,
      t,htag.symm.trans hu,by simpa only [← hl] using hcount,ha hal⟩
  exact ⟨forward _ _ rfl htags hne.mp hlen hboxed.mp hrep.1.mp hrep.2.mp hlabels halign.mp,
    forward _ _ htags htags.symm hne.mpr hlen.symm hboxed.mpr hrep.1.mpr hrep.2.mpr hlabels.symm halign.mpr⟩
end NumberTheoryLean.SourceCandidateFreezing

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

end NumberTheoryLean.LogarithmicBinPartition



namespace NumberTheoryLean.NearbyParentGeometry

open FinitePathGeometry

theorem log_stability {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  have hx0 := hm.trans_le hx
  have hy0 := hm.trans_le hy
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne'] at h
  calc
    Real.log x-Real.log y ≤ (x-y)/y := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    _ ≤ (x-y)/m := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hm hy

end NumberTheoryLean.NearbyParentGeometry



namespace NumberTheoryLean.LogarithmicBinMaps

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SourceStopPredicate PrimeBinRepresentatives RepresentativeAdmission PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure

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



namespace NumberTheoryLean.BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

theorem prime_order_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (p p' q : ℕ) (hp : p ∈ sourcePrimeSet w z) (hp' : p' ∈ sourcePrimeSet w z)
    (hq : q ∈ sourcePrimeSet w z) (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hne : label hw hwz hxi q ≠ label hw hwz hxi p) :
    (p < q ↔ p' < q) ∧ (q < p ↔ q < p') := by
  have bp := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p).mp hp).2
  have bp' := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p').mp hp').2
  have bq := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz q).mp hq).2
  rw [he] at bp'
  have hs := bins_separated hw hwz hxi (label hw hwz hxi p) (label hw hwz hxi q) hne.symm
  rcases hs with hs | hs
  · have h1 : p < q := by exact_mod_cast (show (p:ℝ)<q by linarith)
    have h2 : p' < q := by exact_mod_cast (show (p':ℝ)<q by linarith)
    exact ⟨iff_of_true h1 h2,iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le)⟩
  · have h1 : q < p := by exact_mod_cast (show (q:ℝ)<p by linarith)
    have h2 : q < p' := by exact_mod_cast (show (q:ℝ)<p' by linarith)
    exact ⟨iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le),iff_of_true h1 h2⟩

theorem unique_label_other {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p : ℕ)
    (hc : ((pre++p::tail).map label).count (label p) = 1) :
    ∀ q ∈ pre++tail,label q ≠ label p := by
  have h0 : ((pre++tail).map label).count (label p) = 0 := by
    simp only [List.map_append,List.map_cons,List.count_append,List.count_cons_self] at hc ⊢
    omega
  intro q hq he
  have hm : label p ∈ (pre++tail).map label := List.mem_map.mpr ⟨q,hq,he⟩
  have hh := List.count_pos_iff.mpr hm
  omega

theorem decreasing_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (pre tail : List ℕ) (p p' : ℕ)
    (hall : ∀ q ∈ pre++p::tail,q ∈ sourcePrimeSet w z)
    (hp' : p' ∈ sourcePrimeSet w z)
    (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hc : ((pre++p::tail).map (label hw hwz hxi)).count (label hw hwz hxi p) = 1) :
    (pre++p::tail).Pairwise (· > ·) ↔ (pre++p'::tail).Pairwise (· > ·) := by
  have hp := hall p (by simp)
  have hother := unique_label_other (label hw hwz hxi) pre tail p hc
  have hqall (q : ℕ) (hq : q ∈ pre++tail) : q ∈ sourcePrimeSet w z := by
    apply hall q
    simp only [List.mem_append,List.mem_cons] at hq ⊢
    tauto
  have horder (q : ℕ) (hq : q ∈ pre++tail) :=
    prime_order_replacement hw hwz hxi p p' q hp hp' (hqall q hq) he (hother q hq)
  simp only [List.pairwise_append,List.pairwise_cons]
  constructor
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mp (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mp (hcross q hq p (by simp))
      · exact hcross q hq r (by simp [hr])
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mpr (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mpr (hcross q hq p' (by simp))
      · exact hcross q hq r (by simp [hr])

end NumberTheoryLean.BinReplacementOrder



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

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.JacobsthalSourceScale

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

end ErdosCorrectionLimit

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HypotheticalPairRows
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


section

open _root_.Filter
namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts

theorem source_all_search_units (Cs : ℝ) :
    ∀ᶠ w : ℝ in atTop, 1 < w ∧ ∀ (R : ℝ) (r : ℚ) (p : ℕ),
      0 < R → (r.den : ℝ) ≤ w^Cs → w^((1/4 : ℝ)) ≤ Real.log R/Real.log w →
      R ≤ (p : ℝ) → p.Prime → r.den.Coprime p := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually_gt_atTop Cs
  filter_upwards [hpow, eventually_gt_atTop (1 : ℝ)] with w hCs hw
  refine ⟨hw, ?_⟩
  intro R r p hR hden hsearch hRp hp
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos hw
  have hexp : w^(w^((1/4 : ℝ))) ≤ R := by
    have h := (le_div_iff₀ hL).mp hsearch
    rw [Real.rpow_def_of_pos hw0]
    calc
      _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by nlinarith [h])
      _ = R := Real.exp_log hR
  have hstrict : w^Cs < w^(w^((1/4 : ℝ))) := Real.rpow_lt_rpow_of_exponent_lt hw hCs
  have hdp : r.den < p := by
    exact_mod_cast hden.trans_lt (hstrict.trans_le (hexp.trans hRp))
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hdp) (Nat.le_of_dvd r.den_pos hd)

end ErdosHypotheticalTag

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

namespace NumberTheoryLean.LastPrimeModulusCount
open PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedCountAdapters
open ReferencePruning SievePartition LargePrimeDeletion LogarithmicBinPartition ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem survivor_required_union (Y : ℕ) (H small P : Finset ℕ) (a : ℕ → ℕ) :
    survivors (residueCandidates Y H small a) P (residueBad a)=residueCandidates Y H (small∪P) a := by
  ext n
  simp only [mem_survivors,mem_residueCandidates,Finset.mem_union,or_imp,forall_and]
  tauto

theorem below_all_last (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·)) (q : ℕ) :
    (∀ p∈ps,q<p) ↔ q<ps.getLastD 0 := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  constructor
  · intro h
    exact h _ (List.getLast_mem hne)
  · intro h p hp
    have hd' : (ps.dropLast++[ps.getLast hne]).Pairwise (· > ·) := by rwa [List.dropLast_append_getLast]
    rw [← List.dropLast_append_getLast hne] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.trans ((List.pairwise_append.mp hd').2.2 p hp _ (by simp))
    · simpa only [List.mem_singleton.mp hp] using h

theorem small_suffix_strict_cutoff {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·))
    (hsource : ∀ p∈ps,p∈sourcePrimeSet w top) :
    cutoffPrimes ⌊w⌋₊∪suffixPrimes (sourcePrimeSet w top) ps=cutoffPrimes (ps.getLastD 0-1) := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  have hlast : ps.getLastD 0∈ps := by rw [he]; exact List.getLast_mem hne
  have hP := (mem_sourcePrimeSet hw htop _).mp (hsource _ hlast)
  ext q
  constructor
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨hqprime,hqw⟩ := mem_cutoffPrimes.mp hq
      have hqr : (q:ℝ) < (ps.getLastD 0:ℝ) := ((Nat.le_floor_iff hw.le).mp hqw).trans_lt hP.2.1
      have hqn : q < ps.getLastD 0 := by exact_mod_cast hqr
      exact mem_cutoffPrimes.mpr ⟨hqprime,by omega⟩
    · obtain ⟨hqS,hall⟩ := Finset.mem_filter.mp hq
      have hqprime := ((mem_sourcePrimeSet hw htop q).mp hqS).1
      have hlastq := (below_all_last ps hne hd q).mp hall
      exact mem_cutoffPrimes.mpr ⟨hqprime,by omega⟩
  · intro hq
    obtain ⟨hqprime,hql⟩ := mem_cutoffPrimes.mp hq
    have hPlast : 0 < ps.getLastD 0 := hP.1.pos
    have hqP : q < ps.getLastD 0 := by omega
    by_cases hqw : q ≤ ⌊w⌋₊
    · exact Finset.mem_union_left _ (mem_cutoffPrimes.mpr ⟨hqprime,hqw⟩)
    · have hwq : w < (q:ℝ) := lt_of_not_ge (fun h => hqw ((Nat.le_floor_iff hw.le).mpr h))
      have hqt : (q:ℝ) ≤ top := (show (q:ℝ) ≤ (ps.getLastD 0:ℝ) by exact_mod_cast hqP.le).trans hP.2.2
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(mem_sourcePrimeSet hw htop q).mpr ⟨hqprime,hwq,hqt⟩,(below_all_last ps hne hd q).mpr hqP⟩)

theorem after_survivors_eq_last_modulusCount (Y : ℕ) {w top : ℝ}
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : Node) (mu : ℝ)
    (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·))
    (hsource : ∀ p∈ps,p∈sourcePrimeSet w top) :
    countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)=
      (modulusCount Y (cutoffPrimes (ps.getLastD 0-1)) a ps.prod:ℝ) := by
  have hprime : ∀ p∈ps.toFinset,p.Prime := fun p hp =>
    ((mem_sourcePrimeSet hw htop p).mp (hsource p (List.mem_toFinset.mp hp))).1
  have hprod : (∏ p∈ps.toFinset,p)=ps.prod := by
    simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) (hd.imp (fun h => ne_of_gt h))
  have hfac : ps.prod.primeFactors=ps.toFinset := by
    rw [← hprod]
    exact primeFactors_product ps.toFinset hprime
  unfold countSurvivors
  rw [after_required,after_available]
  change ((survivors (residueCandidates Y (∅∪ps.toFinset) (cutoffPrimes ⌊w⌋₊) a)
    (suffixPrimes (sourcePrimeSet w top) ps) (residueBad a)).card:ℝ)=_
  rw [Finset.empty_union,survivor_required_union,small_suffix_strict_cutoff hw htop ps hne hd hsource]
  simp only [modulusCount,modulusCandidates,Int.cast_natCast,hfac]

theorem frozen_survivors_eq_modulusCount (Y : ℕ) {w top : ℝ}
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : Node) (mu : ℝ)
    (pre tail : List ℕ) (p : ℕ) (htail : tail≠[])
    (hd : (pre++p::tail).Pairwise (· > ·))
    (hsource : ∀ q∈pre++p::tail,q∈sourcePrimeSet w top) :
    countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (pre++p::tail))=
      (modulusCount Y (cutoffPrimes (tail.getLastD 0-1)) a (p*(pre.prod*tail.prod)):ℝ) := by
  have hlast : (pre++p::tail).getLastD 0=tail.getLastD 0 := by
    rw [← List.dropLast_append_getLast htail]
    rw [← List.cons_append,← List.append_assoc]
    simp only [List.getLastD_concat]
  rw [after_survivors_eq_last_modulusCount Y hw htop a z mu _ (by simp) hd hsource,hlast]
  congr 2
  simp only [List.prod_append,List.prod_cons]
  ring
end NumberTheoryLean.LastPrimeModulusCount

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

namespace NumberTheoryLean.ActualSourceStopBinding

open _root_.Finset
open FinitePathGeometry PrimeHistories SourceStopPredicate StoppedCountVertex StoppedEvaluation
open StoppedVertexHistory StoppedTraceSets StoppedCountAdapters FlatStoppedIdentity
open ReferenceAdmission ReferencePruning ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem actual_source_stops_first {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    {ps : List ℕ}
    (hp : ps ∈ stopped w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      P.card (rootVertex z ∅ P mu)) :
    (terminal w z ps).side = .even ∧
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps ∧
      ∀ pre tail : List ℕ,ps = pre++tail → tail ≠ [] →
        ¬((terminal w z pre).side = .even ∧
          stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z pre) := by
  have h := FirstStopSemantics.stopped_first w
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z) P.card (rootVertex z ∅ P mu) hp
  simpa only [FirstStopSemantics.FirstStop,lowerStop,after_node,after_past,rootVertex,List.nil_append,and_assoc] using h

end NumberTheoryLean.ActualSourceStopBinding

end

section

namespace NumberTheoryLean.FirstStopFreezing
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open SourceCandidateFreezing RepresentativeTraceInvariance
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters FirstStopSemantics
open ErdosInversePrimeBin ErdosInverseAlignment

theorem firstStop_iff_takes (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ) :
    FirstStop w stop v ps ↔ lowerStop stop (after w v ps) ∧
      ∀ k < ps.length,¬lowerStop stop (after w v (ps.take k)) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro k hk
    apply h.2 (ps.take k) (ps.drop k) (List.take_append_drop k ps).symm
    intro hz
    have hh := congrArg List.length hz
    simp only [List.length_drop,List.length_nil] at hh
    omega
  · rintro ⟨h,hs⟩
    refine ⟨h,?_⟩
    intro pre tail heq htail
    have htpos : 0 < tail.length := List.length_pos_iff.mpr htail
    have hlen : pre.length < ps.length := by rw [heq,List.length_append]; omega
    have hh := hs pre.length hlen
    simpa only [heq,List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using hh

theorem first_source_stop_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (P : Finset ℕ)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') :
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p::tail) ↔
    FirstStop w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z)
      (rootVertex z ∅ P mu) (pre++p'::tail) := by
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z
  let v := rootVertex z ∅ P mu
  have hlen : (pre++p::tail).length = (pre++p'::tail).length := by simp
  have he (k : ℕ) : lowerStop stop (after w v ((pre++p::tail).take k)) ↔
      lowerStop stop (after w v ((pre++p'::tail).take k)) := by
    have hside := terminal_side_length w z z ((pre++p::tail).take k) ((pre++p'::tail).take k) rfl
      (by simp only [List.length_take,hlen])
    have hh := all_prefix_candidate_replacement Y w Cs eta Clen B xi b₀ b₁ lower width label a z
      pre tail p p' ht hc hlabel hp' ha' k
    simp only [lowerStop,after_node,after_past,v,rootVertex,List.nil_append,hside]
    exact and_congr_right (fun _ => hh)
  have hlast := he (pre++p::tail).length
  simp only [List.take_length] at hlast
  rw [hlen,List.take_length] at hlast
  rw [firstStop_iff_takes,firstStop_iff_takes]
  change (lowerStop stop (after w v (pre++p::tail)) ∧ _) ↔
    (lowerStop stop (after w v (pre++p'::tail)) ∧ _)
  rw [hlast]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  rw [hlen,he k]
end NumberTheoryLean.FirstStopFreezing

end

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

theorem stopped_length (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ stopped w stop n v) : ps.length ≤ n := by
  induction n generalizing v ps with
  | zero =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true, if_true,Finset.mem_singleton] using hp
      simp [he]
    · simp [stopped,traces,hs] at hp
  | succ n ih =>
    by_cases hs : lowerStop stop v
    · have he : ps=[] := by simpa only [stopped,traces,hs,ite_true, if_true,Finset.mem_singleton] using hp
      simp [he]
    · simp only [stopped,traces,hs,ite_false, if_false] at hp
      obtain ⟨p,_hp,hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp hps
      exact Nat.succ_le_succ (ih (child w v p) ht)

theorem stopped_of_reference_first (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (ps : List ℕ) (hlen : ps.length ≤ n)
    (href : ps ∈ referencePrefixes w v.available v.node.side v.node.gap)
    (hf : FirstStop w stop v ps) : ps ∈ stopped w stop n v := by
  induction ps generalizing n v with
  | nil =>
    have hs : lowerStop stop v := hf.1
    cases n <;> simp [stopped,traces,hs]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (reference_cons_iff w v p ps).mp href
    have hroot : ¬lowerStop stop v := hf.2 [] (p::ps) rfl (by simp)
    have hfirst : FirstStop w stop (child w v p) ps := by
      refine ⟨hf.1,?_⟩
      intro pre tail heq htail
      exact hf.2 (p::pre) tail (by simp only [List.cons_append,heq]) htail
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hh := ih n (child w v p) (by simpa using hlen) ht hfirst
      simp only [stopped,traces,hroot,ite_false, if_false]
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨ps,hh,rfl⟩⟩

end NumberTheoryLean.StoppedTraceMembership

end

section

namespace NumberTheoryLean.TagBelowStopWindow
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment

theorem source_tag_nonterminal {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (pre tail : List ℕ) (p : ℕ) {t : Tag n}
    (hw : 1 < w) (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b)
    (hwindow : b₁ < w^((1/4:ℝ)))
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hs : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z (pre++p::tail)) :
    tail ≠ [] := by
  intro ht
  subst tail
  have hh := candidate_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) p hc
  have hb := bin_exponent_bounds hw (hlo (label p)) (hwidth (label p)) hh.2.1
  have hr : representative w lower width label p ≤ b₁ := by
    have hx := hs.2.2.2.2.1.2.1
    simpa only [List.getLastD_concat] using hx
  have hsearch := hh.2.2.1
  change w^((1/4:ℝ)) ≤ leftExponent w (lower (label p)) at hsearch
  change rightExponent w (lower (label p)) (width (label p)) ≤ b₁ at hr
  linarith

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

theorem replacement_product (pre tail : List ℕ) (p : ℕ) :
    (pre++p::tail).prod=p*(pre.prod*tail.prod) := by
  rw [List.prod_append,List.prod_cons]
  ac_rfl

end NumberTheoryLean.TagBelowStopWindow

end

section

namespace NumberTheoryLean.ActualFrozenStopFamily
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag
open StoppedCountVertex StoppedVertexHistory StoppedEvaluation StoppedCountAdapters StoppedTraceSets
open FirstStopSemantics StoppedTraceAdmission StoppedTraceMembership FirstStopFreezing
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open BinReplacementOrder ReferenceAdmission ActualSourceStopBinding ErdosInversePrimeBin ErdosInverseAlignment
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

theorem actual_stopped_replacement (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (hwtop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (pre tail : List ℕ) (p p' : ℕ)
    {t : Tag (binCount w top xi)}
    (hs : pre++p::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu))
    (ht : sourceTag (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) hwtop hxi) (sourceClass a) p = some (t.bin,t.rational))
    (hp' : p' ∈ primeBin (lower w top xi t.bin) (width w top xi t.bin))
    (ha' : aligns (sourceClass a) t.rational p') :
    pre++p'::tail ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu) := by
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) hwtop hxi
  let P := sourcePrimeSet w top
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z
  let v := rootVertex z ∅ P mu
  have hw0 : 0 < w := zero_lt_one.trans hw
  have htag := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p hc
  have hnew := (bin_mem_iff_label hw0 hwtop hxi t.bin p').mp hp'
  have hlabel : lab p' = lab p := hnew.2.2.2.trans htag.1
  have hp'own : p' ∈ primeBin (lo (lab p')) (wi (lab p')) := by
    change p' ∈ primeBin (lower w top xi (lab p')) (width w top xi (lab p'))
    have hnewlabel : lab p' = t.bin := hnew.2.2.2
    rw [hnewlabel]
    exact hp'
  have hp'S : p' ∈ P := (mem_sourcePrimeSet hw0 hwtop p').mpr ⟨hnew.1,hnew.2.1,hnew.2.2.1⟩
  have href := trace_reference_member w stop P.card v (Or.inr hs)
  have hD := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  have hall : ∀ q ∈ pre++p::tail,q ∈ P := hD.2
  have hf := stopped_first w stop P.card v hs
  have hcand : stop (pre++p::tail) := by
    have hh := hf.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hcount : ((pre++p::tail).map lab).count (lab p)=1 := by
    obtain ⟨u,hu,huCount,_huAlign⟩ := hcand.2.2.2.2.2
    have hut : u=t := Option.some.inj (hu.symm.trans ht)
    subst u
    rw [← htag.1]
    exact huCount
  have hdec := (decreasing_replacement hw0 hwtop hxi pre tail p p' hall hp'S hlabel hcount).mp hD.1
  have hfirst : FirstStop w stop v (pre++p'::tail) :=
    (first_source_stop_replacement Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P pre tail p p'
      ht hc hlabel hp'own ha').mp hf
  have hnewCand : stop (pre++p'::tail) := by
    have hh := hfirst.1.2
    simpa only [after_past,v,rootVertex,List.nil_append] using hh
  have hadmit := candidate_admitted Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z (pre++p'::tail)
    hw hC hxi.le (fun i => endpoint_pos hw0 _) (fun i => (effectiveWidth_pos hw0 hwtop hxi).le) hnewCand
  have hmem : ∀ q ∈ pre++p'::tail,q ∈ P :=
    (ActualTagFreezing.forall_mem_replacement_iff (fun q => q ∈ P) pre tail p p'
      (hall p (by simp)) hp'S).mp hall
  apply stopped_of_reference_first w stop P.card v (pre++p'::tail)
  · have hl := stopped_length w stop P.card v hs
    simpa only [List.length_append,List.length_cons] using hl
  · exact Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨hdec,hmem⟩,hadmit⟩
  · exact hfirst

end NumberTheoryLean.ActualFrozenStopFamily

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FrozenPrimeGroup
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FrozenPrimeGroup
open _root_.Finset FiniteFirstTag ActualSourceTags ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass
open StoppedVertexHistory
attribute [local instance] Classical.propDecidable

theorem replacement_injective (pre tail : List ℕ) : Function.Injective (fun p : ℕ => pre++p::tail) := by
  intro p q hpq
  exact (List.cons.inj (List.append_cancel_left hpq)).1

theorem mem_frozenGroup (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail ps : List ℕ) :
    ps ∈ frozenGroup R xi a q pre tail ↔
      ∃ p ∈ primeBin R xi,aligns a q p ∧ ps=pre++p::tail := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
    obtain ⟨hb,ha⟩ := Finset.mem_filter.mp hp
    exact ⟨p,hb,ha,he.symm⟩
  · rintro ⟨p,hp,ha,rfl⟩
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,ha⟩,rfl⟩

end NumberTheoryLean.FrozenPrimeGroup

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FrozenSuffixData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FrozenSuffixData
open PrimeHistories StoppedVertexHistory StoppedCountVertex ReferencePruning

theorem terminal_suffix_cutoff (w : ℝ) (z z' : Node) (tail : List ℕ) (htail : tail ≠ []) :
    (terminal w z tail).cutoff=(terminal w z' tail).cutoff ∧
      (terminal w z tail).closed=false ∧ (terminal w z' tail).closed=false := by
  induction tail generalizing z z' with
  | nil => exact False.elim (htail rfl)
  | cons p ps ih =>
    cases ps with
    | nil => simp [terminal,step]
    | cons q qs => exact ih (step w z p) (step w z' p) (by simp)

end NumberTheoryLean.FrozenSuffixData

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SourceStopWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceStopWindow
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open MarkedPrefixTools ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure

theorem candidate_source_primes (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    ∀ p ∈ ps,p ∈ sourcePrimeSet w top := by
  intro p hp
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    (bin_prime_in_source (zero_lt_one.trans hw) htop hxi _ (hc.2.2.1 p hp))

theorem candidate_actual_window (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).gap/(terminal w z ps).cutoff ∧
      (terminal w z ps).gap/(terminal w z ps).cutoff ≤ 218/100 := by
  let rep := representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
  have hsource := candidate_source_primes Y hw htop hxi a z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hp := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hx1 : 1 < primeExponent w (ps.getLastD 0) :=
    (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hp.2.1)
  have hx := source_representative_error hw htop hxi (hsource _ hlast)
  change 0 ≤ rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ∧
    rep (ps.getLastD 0)-primeExponent w (ps.getLastD 0) ≤ xi/Real.log w at hx
  rw [← terminal_lastD w z ps hc.1] at hx hx1
  have hr := source_prefix_movement hw htop hxi hC hcomp z ps hsource hc.2.1
  change 0 ≤ (terminal w z ps).gap-representativeGap rep z.gap ps ∧
    (terminal w z ps).gap-representativeGap rep z.gap ps ≤ 2*Clen*xi at hr
  have hwin := hc.2.2.2.2.1
  exact representative_to_actual_window (r := (terminal w z ps).gap)
    (rrep := representativeGap rep z.gap ps) (x := (terminal w z ps).cutoff) (xrep := rep (ps.getLastD 0))
    (Delta := 2*Clen*xi) (h := xi/Real.log w) (by linarith) (by linarith [hx.1]) (by linarith [hx.2])
    (by linarith [hr.1]) (by linarith [hr.2]) hwin.1 hwin.2.1 hwin.2.2.1 hwin.2.2.2 hsmall
end NumberTheoryLean.SourceStopWindow

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_StopLengthBandGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StopLengthBandGeometry
open NearbyParentGeometry

theorem shifted_ratio_band {r b a : ℝ} (hb : 400 ≤ b) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hlo : 204/100 ≤ r/b) (hhi : r/b ≤ 218/100) :
    2035/1000 ≤ r/b+(a-2)/b ∧ r/b+(a-2)/b ≤ 218/100 := by
  have hbp : 0 < b := by linarith
  have hshift : -(1/200:ℝ) ≤ (a-2)/b := (le_div_iff₀ hbp).mpr (by nlinarith)
  have hshift0 : (a-2)/b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hbp.le
  constructor <;> linarith

theorem bin_log_length_stability {Y q P R xi p p₀ : ℝ}
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (_hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hp : R ≤ p ∧ p ≤ (1+xi)*R) (hp₀ : R ≤ p₀ ∧ p₀ ≤ (1+xi)*R)
    (hlogP : 200 ≤ Real.log P) :
    |Real.log (Y/(p*q))/Real.log P-Real.log (Y/(p₀*q))/Real.log P| ≤ 1/200 := by
  have hp0 := hR.trans_le hp.1
  have hp00 := hR.trans_le hp₀.1
  have hden : 0 < Real.log P := by linarith
  have habs : |p-p₀| ≤ xi*R := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hlog : |Real.log p-Real.log p₀| ≤ xi := by
    have hh := log_stability hR hp.1 hp₀.1
    have hd := div_le_div_of_nonneg_right habs hR.le
    rw [mul_div_cancel_right₀ xi hR.ne'] at hd
    exact hh.trans hd
  have he : Real.log (Y/(p*q))-Real.log (Y/(p₀*q))=Real.log p₀-Real.log p := by
    rw [Real.log_div hY.ne' (mul_pos hp0 hq).ne',Real.log_div hY.ne' (mul_pos hp00 hq).ne',
      Real.log_mul hp0.ne' hq.ne',Real.log_mul hp00.ne' hq.ne']
    ring
  rw [← sub_div,he,abs_div,abs_of_pos hden,abs_sub_comm (Real.log p₀)]
  calc
    _ ≤ xi/Real.log P := div_le_div_of_nonneg_right hlog hden.le
    _ ≤ 1/Real.log P := div_le_div_of_nonneg_right hxi1 hden.le
    _ ≤ 1/200 := one_div_le_one_div_of_le (by norm_num) hlogP

theorem whole_bin_length_band {Y q P R xi p p₀ s₀ : ℝ}
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hp : R ≤ p ∧ p ≤ (1+xi)*R) (hp₀ : R ≤ p₀ ∧ p₀ ≤ (1+xi)*R)
    (hlogP : 200 ≤ Real.log P) (hs₀ : Real.log (Y/(p₀*q))/Real.log P=s₀)
    (hband : 2035/1000 ≤ s₀ ∧ s₀ ≤ 218/100) :
    203/100 ≤ Real.log (Y/(p*q))/Real.log P ∧ Real.log (Y/(p*q))/Real.log P ≤ 219/100 := by
  have hh := bin_log_length_stability hY hq hR hxi hxi1 hp hp₀ hlogP
  rw [hs₀] at hh
  constructor <;> linarith [(abs_le.mp hh).1,(abs_le.mp hh).2]
end NumberTheoryLean.StopLengthBandGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeProductLogCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
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

theorem source_length_exponent_identity {w a : ℝ} (hw : 1 < w) (Y P : ℕ)
    (hY : 0 < Y) (hP : 1 < P) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (P:ℝ)=
      (terminal w z ps).gap/primeExponent w P+(a-2)/primeExponent w P := by
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlogP : 0 < Real.log (P:ℝ) := Real.log_pos (by exact_mod_cast hP)
  rw [terminal_gap_log_quotient Y hY z hroot ps hp,primeExponent]
  field_simp [hlogw.ne',hlogP.ne']
  ring
end NumberTheoryLean.PrimeProductLogCoordinates


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CandidateLengthBand
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateLengthBand
open FinitePathGeometry PrimeHistories SourceStopPredicate SourceStopWindow PrimeProductLogCoordinates
open StopLengthBandGeometry MarkedPrefixTools LogarithmicBinScale LogarithmicBinEndpoints
open LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem candidate_whole_bin_length_band (Y : ℕ) (hY : 0 < Y)
    {w top Cs eta Clen B xi b₀ b₁ alpha : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (hlogw : 1 ≤ Real.log w)
    (hb₀ : 401 ≤ b₀) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (residue : ℕ → ℕ) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-alpha+2) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps)
    (p₀ q : ℕ) (hq : 0 < q) (hprod : ps.prod=p₀*q)
    {R zeta : ℝ} (hR : 0 < R) (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hp₀ : R ≤ (p₀:ℝ) ∧ (p₀:ℝ) ≤ (1+zeta)*R)
    (p : ℝ) (hp : R ≤ p ∧ p ≤ (1+zeta)*R) :
    203/100 ≤ Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ∧
      Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ≤ 219/100 := by
  have hwindow := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hsource := candidate_source_primes Y hw htop hxi residue z ps hc
  have hpos : ∀ p ∈ ps,0 < p := fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hP : 1 < ps.getLastD 0 := hprime.1.one_lt
  have hstep : xi/Real.log w ≤ 1 := (div_le_self hxi.le hlogw).trans hxi1
  have hb : 400 ≤ (terminal w z ps).cutoff := by linarith [hwindow.1]
  have hlogP : 200 ≤ Real.log (ps.getLastD 0:ℝ) := by
    have he : Real.log (ps.getLastD 0:ℝ)=(terminal w z ps).cutoff*Real.log w := by
      rw [terminal_lastD w z ps hc.1,primeExponent,div_mul_cancel₀ _ (Real.log_pos hw).ne']
    rw [he]
    nlinarith
  have hid := source_length_exponent_identity hw Y (ps.getLastD 0) hY hP z hroot ps hpos
  rw [← terminal_lastD w z ps hc.1] at hid
  have hband : 2035/1000 ≤ Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) ∧
      Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) ≤ 218/100 := by
    rw [hid]
    exact shifted_ratio_band hb ha0 ha1 hwindow.2.2.1 hwindow.2.2.2
  have he₀ : Real.log ((Y:ℝ)/((p₀:ℝ)*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ)=
      Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) := by rw [hprod,Nat.cast_mul]
  exact whole_bin_length_band (by exact_mod_cast hY) (by exact_mod_cast hq) hR hzeta hzeta1 hp hp₀ hlogP he₀ hband
end NumberTheoryLean.CandidateLengthBand


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_MovingStopBandParameters
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MovingStopBandParameters
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MarkedPrefixTools MarkedSourceSmallness ErdosPrimeInputs.HarmonicPrimeMeasure

theorem moving_stop_band_conditions (Clen xi : ℝ) (hxi : 0 ≤ xi) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ 1 ≤ Real.log w ∧ 401 ≤ K*(Real.log w)^2 ∧
      2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2) ∧
      xi/Real.log w ≤ (K*(Real.log w)^2)/2 := by
  let M := max 401 (max (2*xi) (50*(2*Clen*xi+(218/100)*xi)+1))
  filter_upwards [moving_compact_gap_small (6*M) hK,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hm hlog hw
  have hb : M < K*(Real.log w)^2 := by linarith
  have h₁ : (401:ℝ) ≤ M := le_max_left _ _
  have h₂ : 2*xi ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 50*(2*Clen*xi+(218/100)*xi)+1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hd := div_le_self hxi hlog
  exact ⟨hw,hlog,by linarith,by linarith,by linarith⟩

theorem last_prime_cutoff_power {w : ℝ} (hw : 1 < w) (z : Node) (ps : List ℕ)
    (hne : ps ≠ []) (hP : 0 < (ps.getLastD 0:ℝ)) :
    w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hw),terminal_lastD w z ps hne,primeExponent]
  have he : Real.log w*(Real.log (ps.getLastD 0:ℝ)/Real.log w)=Real.log (ps.getLastD 0:ℝ) := by
    field_simp [(Real.log_pos hw).ne']
  rw [he,Real.exp_log hP]

theorem candidate_moving_last_prime_lower (Y : ℕ) {w top Cs eta Clen B xi K b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2))
    (hhalf : xi/Real.log w ≤ (K*(Real.log w)^2)/2)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
      w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  have hwindow := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hsource := candidate_source_primes Y hw htop hxi residue z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hP : 0 < (ps.getLastD 0:ℝ) := by exact_mod_cast hprime.1.pos
  refine ⟨?_,last_prime_cutoff_power hw z ps hc.1 hP⟩
  have hcut : (K*(Real.log w)^2)/2 ≤ (terminal w z ps).cutoff := by linarith [hwindow.1]
  have hlogP : Real.log (ps.getLastD 0:ℝ)=(terminal w z ps).cutoff*Real.log w := by
    rw [terminal_lastD w z ps hc.1,primeExponent,div_mul_cancel₀ _ (Real.log_pos hw).ne']
  rw [← Real.exp_log hP]
  apply Real.exp_le_exp.mpr
  calc
    _ = ((K*(Real.log w)^2)/2)*Real.log w := by ring
    _ ≤ (terminal w z ps).cutoff*Real.log w := mul_le_mul_of_nonneg_right hcut (Real.log_pos hw).le
    _ = _ := hlogP.symm
end NumberTheoryLean.MovingStopBandParameters


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualRepeatedBinStep
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateTerminalGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters FrozenSuffixData
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_ratio_div_cutoff (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ [])
    (hx : (terminal w z ps).cutoff ≠ 0) :
    (terminal w z ps).ratio=(terminal w z ps).gap/(terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      change primeExponent w p ≠ 0 at hx
      change PrimeTiltGeometry.childRatio w z.gap p=(z.gap-primeExponent w p)/primeExponent w p
      unfold PrimeTiltGeometry.childRatio
      field_simp [hx]
    | cons q qs => exact ih (step w z p) (by simp) hx

theorem candidate_terminal_geometry (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hpos : 0 < b₀-xi/Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    b₀-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
      204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
      Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false := by
  have hwin := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hx : 0 < (terminal w z ps).cutoff := hpos.trans_le hwin.1
  have hfrac := terminal_ratio_div_cutoff w z ps hc.1 hx.ne'
  have hlo : 204/100 ≤ (terminal w z ps).ratio := by rw [hfrac]; exact hwin.2.2.1
  have hhi : (terminal w z ps).ratio ≤ 218/100 := by rw [hfrac]; exact hwin.2.2.2
  have hcons : Consistent (terminal w z ps) := by
    apply (eq_div_iff (show (terminal w z ps).ratio ≠ 0 by linarith)).mpr
    have hh := (eq_div_iff hx.ne').mp hfrac
    nlinarith
  exact ⟨hwin.1,hwin.2.1,hlo,hhi,hcons,(terminal_suffix_cutoff w z z ps hc.1).2.1⟩
end NumberTheoryLean.CandidateTerminalGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagSmallPrimeData
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosStoppedTagSieve
open ErdosUnitLifts
attribute [local instance] Classical.propDecidable

lemma mem_smallPrimeSet (P : ℝ) (t : ℕ) : t∈smallPrimeSet P ↔ t.Prime ∧ (t:ℝ)<P := by
  simp only [smallPrimeSet,Finset.mem_filter,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,ht⟩,hP⟩
    exact ⟨ht,hP⟩
  · rintro ⟨ht,hP⟩
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
    exact ⟨⟨(Nat.le_floor_iff (by linarith)).mpr hP.le,ht⟩,hP⟩

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeWordArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  ErdosInverseCounts ErdosInverseAlignment ErdosHypotheticalTag
  ErdosPrimeInputs.MertensStrong NumberTheoryLean

attribute [local instance] Classical.propDecidable

theorem strict_smallPrimeSet_nat (P : ℕ) :
    smallPrimeSet (P : ℝ)=LargePrimeDeletion.cutoffPrimes (P-1) := by
  ext t
  rw [mem_smallPrimeSet,LargePrimeDeletion.mem_cutoffPrimes]
  constructor
  · rintro ⟨ht,hlt⟩
    have hlt' : t < P := by exact_mod_cast hlt
    exact ⟨ht,by omega⟩
  · rintro ⟨ht,hle⟩
    have hlt : t < P := by have := ht.two_le;omega
    exact ⟨ht,by exact_mod_cast hlt⟩

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open ErdosInverseCounts ErdosInverseAlignment ErdosStoppedTagSieve
  NumberTheoryLean.LastPrimeModulusCount


theorem prime_word_product (ps : List ℕ) (hd : ps.Pairwise (· > ·))
    (hprime : ∀ p ∈ ps,p.Prime) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ps.prod.primeFactors=ps.toFinset := by
  have hn : ps.Nodup := hd.imp (fun h => ne_of_gt h)
  have hpos : 0 < ps.prod := List.prod_pos (fun p hp => (hprime p hp).pos)
  have he : (∏ p ∈ ps.toFinset,p)=ps.prod := by
    simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) hn
  have hprimeF : ∀ p ∈ ps.toFinset,p.Prime := fun p hp => hprime p (List.mem_toFinset.mp hp)
  have hsq : Squarefree (∏ p ∈ ps.toFinset,p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      simp only [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprimeF p hp) (hprimeF q hq)).mpr hpq
    · exact fun p hp => (hprimeF p hp).squarefree
  refine ⟨hpos,by rwa [he] at hsq,?_⟩
  rw [← he]
  exact primeFactors_product ps.toFinset hprimeF

theorem last_prime_mem (ps : List ℕ) (hne : ps≠[]) : ps.getLastD 0 ∈ ps := by
  rw [← List.dropLast_append_getLast hne,List.getLastD_concat]
  simp

theorem fixed_tail_arithmetic (pre tail : List ℕ) (p : ℕ) (htail : tail ≠ [])
    (hd : (pre++p::tail).Pairwise (· > ·))
    (hprime : ∀ t ∈ pre++p::tail,t.Prime) (a : ℕ → ℤ) (r : ℚ)
    (hAlign : ∀ t ∈ pre++tail,aligns a r t) :
    (tail.getLastD 0).Prime ∧ 0 < pre.prod*tail.prod ∧
      Squarefree (p*(pre.prod*tail.prod)) ∧
      (∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,tail.getLastD 0 ≤ t) ∧
      p ∉ smallPrimeSet (tail.getLastD 0 : ℝ) ∧
      (∀ t ∈ smallPrimeSet (tail.getLastD 0 : ℝ),(pre.prod*tail.prod).Coprime t) ∧
      ∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,t ≠ p → aligns a r t := by
  have hLastTail := last_prime_mem tail htail
  have hLast : (tail.getLastD 0).Prime := hprime _
    (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hLastTail))))
  have hprod := prime_word_product (pre++p::tail) hd hprime
  have he : (pre++p::tail).prod=p*(pre.prod*tail.prod) := by
    simp only [List.prod_append,List.prod_cons] <;> ring
  rw [he] at hprod
  have hqpos : 0 < pre.prod*tail.prod := by
    by_contra hn
    have hz : pre.prod*tail.prod=0 := by omega
    have hh := hprod.1
    rw [hz,mul_zero] at hh
    omega
  have hlastWord : (pre++p::tail).getLastD 0=tail.getLastD 0 := by
    rw [← List.dropLast_append_getLast htail]
    rw [← List.cons_append,← List.append_assoc]
    simp only [List.getLastD_concat]
  have hlow : ∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,tail.getLastD 0 ≤ t := by
    have hh := (below_all_last (pre++p::tail) (by simp) hd (tail.getLastD 0-1)).mpr
      (by rw [hlastWord];exact Nat.sub_lt hLast.pos (by norm_num))
    intro t ht
    rw [hprod.2.2] at ht
    have h := hh t (List.mem_toFinset.mp ht)
    omega
  have hPp : tail.getLastD 0 < p :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hd).2.1).1 _ hLastTail
  refine ⟨hLast,hqpos,hprod.2.1,hlow,?_,?_,?_⟩
  · intro hp
    have hh := ((mem_smallPrimeSet _ p).mp hp).2
    have hpp : (tail.getLastD 0 : ℝ) < p := by exact_mod_cast hPp
    linarith
  · intro t ht
    obtain ⟨htPrime,htP⟩ := (mem_smallPrimeSet _ t).mp ht
    apply Nat.Coprime.symm
    apply htPrime.coprime_iff_not_dvd.mpr
    intro htq
    have htd : t ∣ p*(pre.prod*tail.prod) := dvd_mul_of_dvd_right htq p
    have htf : t ∈ (p*(pre.prod*tail.prod)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨htPrime,htd,hprod.1.ne'⟩
    have h := hlow t htf
    have htP' : t < tail.getLastD 0 := by exact_mod_cast htP
    omega
  · intro t ht hne
    rw [hprod.2.2] at ht
    have hm := List.mem_toFinset.mp ht
    apply hAlign t
    simp only [List.mem_append,List.mem_cons] at hm ⊢
    tauto

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalKeyWitness
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalStopKey
open ActualSourceTags ActualTagFreezing FiniteFirstTag
open SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment


theorem stopKey_of_tagged_word {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p : ℕ) {t : Tag n}
    (ht : sourceTag Y w Cs eta lower width label a (pre++p::tail)=some t)
    (hi : t.index=pre.length) :
    stopKey Y w Cs eta lower width label a (pre++p::tail)=some ⟨t,pre,tail⟩ := by
  simp [stopKey,ht,hi,List.take_append,List.drop_append]

theorem stopKey_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {k : Key n}
    (hk : stopKey Y w Cs eta lower width label a ps=some k) :
    ∃ p : ℕ,ps=k.pre++p::k.tail ∧ k.tag.index=k.pre.length ∧
      sourceTag Y w Cs eta lower width label a ps=some k.tag ∧
      tagCandidate Y w Cs eta lower width label a p=some (k.tag.bin,k.tag.rational) := by
  cases ht : sourceTag Y w Cs eta lower width label a ps with
  | none => simp [stopKey,ht] at hk
  | some t =>
    obtain ⟨pre,p,tail,heq,hi,hp,_hbefore⟩ := firstTagFrom_witness
      (tagCandidate Y w Cs eta lower width label a) 0 ps ht
    have hi' : t.index=pre.length := by simpa only [zero_add] using hi
    have hkey : stopKey Y w Cs eta lower width label a ps=some ⟨t,pre,tail⟩ := by
      rw [heq]
      exact stopKey_of_tagged_word Y w Cs eta lower width label a pre tail p (by simpa only [heq] using ht) hi'
    have he : k=⟨t,pre,tail⟩ := Option.some.inj (hk.symm.trans hkey)
    subst k
    exact ⟨p,heq,hi',rfl,hp⟩

theorem stopKey_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {k : Key n}
    (hk : stopKey Y w Cs eta lower width label a ps=some k) (p' : ℕ)
    (hl : label p'=k.tag.bin)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns a k.tag.rational p') :
    stopKey Y w Cs eta lower width label a (k.pre++p'::k.tail)=some k := by
  obtain ⟨p,heq,hi,ht,hp⟩ := stopKey_witness Y w Cs eta lower width label a ps hk
  have hwit := candidate_witness Y w Cs eta lower width label a p hp
  have he := sourceTag_replacement Y w Cs eta lower width label a k.pre k.tail p p'
    hp (hl.trans hwit.1) hp' ha'
  have ht' : sourceTag Y w Cs eta lower width label a (k.pre++p'::k.tail)=some k.tag :=
    he.symm.trans (by simpa only [heq] using ht)
  have hh := stopKey_of_tagged_word Y w Cs eta lower width label a k.pre k.tail p' ht' hi
  exact hh
end NumberTheoryLean.CanonicalStopKey



namespace NumberTheoryLean.ActualStopGroupFiber
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag CanonicalStopKey
open StoppedCountAdapters StoppedTraceSets ActualSourceStopBinding ActualFrozenStopFamily
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open FrozenPrimeGroup ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem key_some_of_mem (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hps : ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) :
    ∃ k,key Y w top Cs eta xi hw htop hxi a ps=some k := by
  have hh := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu (lower w top xi)
    (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z (sourcePrimeSet w top) hps
  obtain ⟨t,ht,_hc,_ha⟩ := hh.2.1.2.2.2.2.2
  refine ⟨⟨t,ps.take t.index,ps.drop (t.index+1)⟩,?_⟩
  simp only [key,stopKey,ht,Option.map_some]

theorem key_mem_group (Y : ℕ) (w top Cs eta xi : ℝ) (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (a : ℕ → ℕ) (ps : List ℕ) {k : Key (binCount w top xi)}
    (hk : key Y w top Cs eta xi hw htop hxi a ps=some k) : ps ∈ keyGroup w top xi a k := by
  obtain ⟨p,heq,_hi,_ht,hp⟩ := stopKey_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk
  have hc := candidate_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) p hp
  apply (mem_frozenGroup _ _ _ _ _ _ ps).mpr
  refine ⟨p,?_,hc.2.2.2.2,heq⟩
  rw [hc.1]
  exact hc.2.1

theorem group_eq_fiber (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (k : Key (binCount w top xi))
    (hpresent : ∃ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
      key Y w top Cs eta xi hw htop hxi a ps=some k) :
    keyGroup w top xi a k=(family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).filter
      (fun ps => key Y w top Cs eta xi hw htop hxi a ps=some k) := by
  obtain ⟨ps,hps,hk⟩ := hpresent
  obtain ⟨p,heq,hi,ht,hp⟩ := stopKey_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk
  apply Finset.ext
  intro qs
  constructor
  · intro hqs
    obtain ⟨p',hp',ha',rfl⟩ := (mem_frozenGroup _ _ _ _ _ _ qs).mp hqs
    have hnew := (bin_mem_iff_label (zero_lt_one.trans hw) htop hxi k.tag.bin p').mp hp'
    have hown : p' ∈ primeBin (lower w top xi (label (zero_lt_one.trans hw) htop hxi p'))
        (width w top xi (label (zero_lt_one.trans hw) htop hxi p')) := by
      rw [hnew.2.2.2]
      exact hp'
    have hnewkey := stopKey_replacement (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk p' hnew.2.2.2 hown ha'
    refine Finset.mem_filter.mpr ⟨?_,hnewkey⟩
    subst ps
    exact actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z
      k.pre k.tail p p' hps ht hp hp' ha'
  · intro hqs
    exact key_mem_group Y w top Cs eta xi hw htop hxi a qs (Finset.mem_filter.mp hqs).2
end NumberTheoryLean.ActualStopGroupFiber



namespace NumberTheoryLean.CanonicalStopPartition
open PrimeHistories CanonicalStopKey ActualStopGroupFiber

attribute [local instance] Classical.propDecidable

theorem mem_keys (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node)
    (k : Key (LogarithmicBinScale.binCount w top xi)) :
    k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z ↔
      ∃ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
        key Y w top Cs eta xi hw htop hxi a ps=some k := by
  simp [keys]

theorem groups_disjoint (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node)
    {k l : Key (LogarithmicBinScale.binCount w top xi)}
    (hk : k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z)
    (hl : l ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) (hne : k ≠ l) :
    Disjoint (keyGroup w top xi a k) (keyGroup w top xi a l) := by
  rw [group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k
    ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mp hk),
    group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z l
    ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l).mp hl)]
  apply Finset.disjoint_left.mpr
  intro ps hps hps'
  exact hne (Option.some.inj ((Finset.mem_filter.mp hps).2.symm.trans (Finset.mem_filter.mp hps').2))

theorem groups_union (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node) :
    (keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).biUnion (keyGroup w top xi a)=
      family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z := by
  ext ps
  constructor
  · intro hps
    obtain ⟨k,hk,hmem⟩ := Finset.mem_biUnion.mp hps
    rw [group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k
      ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mp hk)] at hmem
    exact (Finset.mem_filter.mp hmem).1
  · intro hps
    obtain ⟨k,hk⟩ := key_some_of_mem Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z ps hps
    exact Finset.mem_biUnion.mpr ⟨k,(mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mpr ⟨ps,hps,hk⟩,
      key_mem_group Y w top Cs eta xi hw htop hxi a ps hk⟩

theorem sum_over_groups (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node)
    (F : List ℕ → ℝ) :
    (∑ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,F ps)=
      ∑ k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,∑ ps ∈ keyGroup w top xi a k,F ps := by
  rw [← groups_union Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z]
  apply Finset.sum_biUnion
  intro k hk l hl hne
  exact groups_disjoint Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z hk hl hne
end NumberTheoryLean.CanonicalStopPartition



namespace NumberTheoryLean.CanonicalKeyWitness
open PrimeHistories CanonicalStopKey CanonicalStopPartition ActualStopGroupFiber
open SourceStopPredicate ActualSourceTags ActualBinOwners ActualSourceStopBinding TagBelowStopWindow
open StoppedCountAdapters StoppedTraceSets StoppedTraceAdmission
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem key_witness_exists {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ mu : ℝ) (a : ℕ → ℕ) (z : Node)
    (hwindow : b₁ < w^((1/4:ℝ))) (k : Key (binCount w top xi))
    (hk : k∈keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) :
    Nonempty (Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k) := by
  obtain ⟨ps,hps,hkey⟩ := (mem_keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z k).mp hk
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) htop hxi
  let P := sourcePrimeSet w top
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z
  obtain ⟨p₀,heq,hindex,htag,hptag⟩ := stopKey_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) ps hkey
  have hstop := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P hps
  have href := trace_reference_member w stop P.card (rootVertex z ∅ P mu) (Or.inr hps)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  obtain ⟨t,ht,hsingle,helig,hnear,halign⟩ := candidate_owner_witness Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z ps hw hstop.2.1
  have he : t=k.tag := Option.some.inj (ht.symm.trans htag)
  subst t
  subst ps
  have hp := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p₀ hptag
  have htail := source_tag_nonterminal (t:=k.tag) Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z k.pre k.tail p₀
    hw (fun b => endpoint_pos (zero_lt_one.trans hw) b.1)
    (fun _ => (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le) hwindow hptag hstop.2.1
  refine ⟨{
    p₀ := p₀
    mem_family := hps
    candidate := hstop.2.1
    tag := htag
    prime_tag := hptag
    index := hindex
    ordered := hd.1
    source := hd.2
    singleton := hsingle
    eligible := helig
    near_full := hnear
    aligned := halign
    prime_bin := ?_
    bin_eq := hp.1
    search := ?_
    owner := ?_
    tail_nonempty := htail }⟩
  · simpa only [← hp.1] using hp.2.1
  · simpa only [← hp.1] using hp.2.2.1
  · simpa only [← hp.1] using hp.2.2.2.1
end NumberTheoryLean.CanonicalKeyWitness


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCorrectionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalKeyReplacement
open PrimeHistories CanonicalStopKey CanonicalKeyWitness ActualStopGroupFiber
open SourceStopPredicate ActualTagFreezing ActualFrozenStopFamily BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment


variable {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
  {Y : ℕ} {Cs eta Clen B b₀ b₁ mu : ℝ} {a : ℕ → ℕ} {z : Node}
  {k : Key (binCount w top xi)} (d : Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k)

include d

theorem whole_bin_words (p : ℕ) (hp : p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)) :
    (k.pre++p::k.tail).Pairwise (· > ·) ∧
      ∀ q∈k.pre++p::k.tail,q∈sourcePrimeSet w top := by
  have hn := (bin_mem_iff_label (zero_lt_one.trans hw) htop hxi k.tag.bin p).mp hp
  have hpS : p∈sourcePrimeSet w top := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    ⟨hn.1,hn.2.1,hn.2.2.1⟩
  have hl : label (zero_lt_one.trans hw) htop hxi p=label (zero_lt_one.trans hw) htop hxi d.p₀ := hn.2.2.2.trans d.bin_eq
  have hc : ((k.pre++d.p₀::k.tail).map (label (zero_lt_one.trans hw) htop hxi)).count
      (label (zero_lt_one.trans hw) htop hxi d.p₀)=1 := by rw [← d.bin_eq]; exact d.singleton
  have hD := (decreasing_replacement (zero_lt_one.trans hw) htop hxi k.pre k.tail d.p₀ p d.source hpS hl hc).mp d.ordered
  have hS := (forall_mem_replacement_iff (fun q => q∈sourcePrimeSet w top) k.pre k.tail d.p₀ p
    (d.source d.p₀ (by simp)) hpS).mp d.source
  exact ⟨hD,hS⟩

theorem fixed_other_alignment : ∀ q∈k.pre++k.tail,aligns (sourceClass a) k.tag.rational q := by
  intro q hq
  apply d.aligned q
  simp only [List.mem_append,List.mem_cons] at hq ⊢
  tauto

theorem fixed_cofactor_pos : 0 < k.pre.prod*k.tail.prod := by
  have hs : ∀ q∈k.pre++k.tail,0 < q := by
    intro q hq
    have hm : q∈k.pre++d.p₀::k.tail := by
      simp only [List.mem_append,List.mem_cons] at hq ⊢
      tauto
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (d.source q hm)).1.pos
  simpa only [List.prod_append] using List.prod_pos hs

theorem search_lower : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ lower w top xi k.tag.bin := by
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have hs : w^((1:ℝ)/4) ≤ Real.log (lower w top xi k.tag.bin)/Real.log w := d.search
  have hh := Real.exp_le_exp.mpr ((le_div_iff₀ (Real.log_pos hw)).mp hs)
  simpa only [Real.exp_log hR] using hh
end NumberTheoryLean.CanonicalKeyReplacement



namespace NumberTheoryLean.MovingCandidateBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters CandidateTerminalGeometry CandidateLengthBand


theorem moving_candidate_node_window {Clen xi K : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta b₁ : ℝ,
      ∀ (residue : ℕ → ℕ) (z : Node) (ps : List ℕ),
      stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) residue z ps →
      K*(Real.log w)^2-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
        204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
        Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false ∧
        Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
        w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  filter_upwards [moving_stop_band_conditions Clen xi hxi.le hK] with w hcond
  obtain ⟨hw,hlog,hb₀,hsmall,hhalf⟩ := hcond
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta b₁ residue z ps hc
  have hstep : xi/Real.log w ≤ 1 := (div_le_self hxi.le hlog).trans hxi1
  have hpos : 0 < K*(Real.log w)^2-xi/Real.log w := by linarith
  have hn := candidate_terminal_geometry Y hw htop hxi hC hcomp hpos hsmall residue z ps hc
  have hP := candidate_moving_last_prime_lower Y hw htop hxi hC hcomp hsmall hhalf residue z ps hc
  exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2,hP.1,hP.2⟩

theorem moving_candidate_J_band {Clen xi K : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,0 < Y →
      ∀ alpha Cs eta b₁ : ℝ,0 ≤ alpha → alpha ≤ 1 →
      ∀ (residue : ℕ → ℕ) (z : Node),z.gap=Real.log (Y:ℝ)/Real.log w-alpha+2 →
      ∀ ps : List ℕ,
      stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) residue z ps →
      ∀ p₀ q : ℕ,0 < q → ps.prod=p₀*q → ∀ R zeta : ℝ,0 < R → 0 ≤ zeta → zeta ≤ 1 →
      R ≤ (p₀:ℝ) → (p₀:ℝ) ≤ (1+zeta)*R → ∀ p : ℝ,R ≤ p → p ≤ (1+zeta)*R →
      Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
        203/100 ≤ Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ≤ 219/100 := by
  filter_upwards [moving_stop_band_conditions Clen xi hxi.le hK] with w hcond
  obtain ⟨hw,hlog,hb₀,hsmall,hhalf⟩ := hcond
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y hY alpha Cs eta b₁ ha0 ha1 residue z hroot ps hc p₀ q hq hprod R zeta hR hzeta hzeta1 hp₀lo hp₀hi p hplo hphi
  have hBand := candidate_whole_bin_length_band Y hY hw htop hxi hxi1 hC hcomp hlog hb₀ ha0 ha1 hsmall
    residue z hroot ps hc p₀ q hq hprod hR hzeta hzeta1 ⟨hp₀lo,hp₀hi⟩ p ⟨hplo,hphi⟩
  have hP := (candidate_moving_last_prime_lower Y hw htop hxi hC hcomp hsmall hhalf residue z ps hc).1
  exact ⟨hP,hBand⟩
end NumberTheoryLean.MovingCandidateBands



namespace NumberTheoryLean.CanonicalKeyBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories CanonicalStopKey CanonicalKeyWitness CanonicalKeyReplacement
open SourceStopPredicate TagBelowStopWindow MovingCandidateBands
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin
open scoped Topology


theorem last_fixed_tail (pre tail : List ℕ) (p : ℕ) (htail : tail≠[]) :
    (pre++p::tail).getLastD 0=tail.getLastD 0 := by
  rw [← List.dropLast_append_getLast htail,← List.cons_append,← List.append_assoc]
  simp only [List.getLastD_concat]

theorem moving_key_bands {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (_hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,0 < Y →
      ∀ aStar Cs eta mu : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ (a : ℕ → ℕ) (z : Node),
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      ∀ k : Key (binCount w top xi),
      ∀ _d : Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2) mu a z k,
      Real.exp ((Kstop/2)*(Real.log w)^3) ≤ (k.tail.getLastD 0:ℝ) ∧
      (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) ∧
      ∀ p∈Set.Icc (lower w top xi k.tag.bin) ((1+width w top xi k.tag.bin)*lower w top xi k.tag.bin),
        203/100 ≤ Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ≤ 219/100 := by
  filter_upwards [moving_candidate_J_band hC hxi hxi1 hK,moving_candidate_node_window hC hxi hxi1 hK]
    with w hBand hNode
  obtain ⟨hw,hBand⟩ := hBand
  obtain ⟨_hwN,hNode⟩ := hNode
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y hY aStar Cs eta mu ha0 ha1 a z hroot k d
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have htheta : 0 < width w top xi k.tag.bin := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
  have htheta1 : width w top xi k.tag.bin ≤ 1 :=
    (effectiveWidth_le (zero_lt_one.trans hw) htop hxi).trans hxi1
  have hp₀ := (mem_primeBin hR.le htheta.le d.p₀).mp d.prime_bin
  have hq := fixed_cofactor_pos hw htop hxi d
  have hprod := replacement_product k.pre k.tail d.p₀
  have hLast := last_fixed_tail k.pre k.tail d.p₀ d.tail_nonempty
  have hJ (p : ℝ) (hpL : lower w top xi k.tag.bin ≤ p)
      (hpU : p ≤ (1+width w top xi k.tag.bin)*lower w top xi k.tag.bin) :=
    hBand top htop B hcomp Y hY aStar Cs eta (rho*Kstop*(Real.log w)^2) ha0 ha1 a z hroot
      (k.pre++d.p₀::k.tail) d.candidate d.p₀ (k.pre.prod*k.tail.prod) hq hprod
      (lower w top xi k.tag.bin) (width w top xi k.tag.bin) hR htheta.le htheta1 hp₀.2.1.le hp₀.2.2 p hpL hpU
  have hJU : lower w top xi k.tag.bin ≤ (1+width w top xi k.tag.bin)*lower w top xi k.tag.bin := by nlinarith
  have hJR := hJ (lower w top xi k.tag.bin) (le_refl _) hJU
  rw [hLast] at hJR
  obtain ⟨_hlo,hcut,_hrlo,_hrhi,_hcons,_hclosed,_hPlo,hpower⟩ :=
    hNode top htop B hcomp Y Cs eta (rho*Kstop*(Real.log w)^2) a z (k.pre++d.p₀::k.tail) d.candidate
  rw [hLast] at hpower
  have hUpper : (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) := by
    calc
      _ = w^(terminal w z (k.pre++d.p₀::k.tail)).cutoff := hpower.symm
      _ ≤ w^(rho*Kstop*(Real.log w)^2) := Real.rpow_le_rpow_of_exponent_le hw.le hcut
      _ = _ := by rw [Real.rpow_def_of_pos (zero_lt_one.trans hw)]; congr 1; ring
  refine ⟨hJR.1,hUpper,?_⟩
  intro p hp
  have hh := (hJ p hp.1 hp.2).2
  rwa [hLast] at hh
end NumberTheoryLean.CanonicalKeyBands



namespace ErdosStoppedArithmetic
open NumberTheoryLean NumberTheoryLean.FrozenPrimeGroup NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedVertexHistory NumberTheoryLean.StoppedCountAdapters
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion
  NumberTheoryLean.LastPrimeModulusCount
  ErdosInverseAlignment ErdosInversePrimeBin ErdosInverseCounts

attribute [local instance] Classical.propDecidable

theorem frozen_group_reward_sum (R theta : ℝ) (a : ℕ → ℤ) (r : ℚ)
    (pre tail : List ℕ) (reward : List ℕ → ℝ) :
    (∑ ps ∈ frozenGroup R theta a r pre tail,reward ps)=
      ∑ p ∈ (primeBin R theta).filter (aligns a r),reward (pre++p::tail) := by
  rw [frozenGroup,Finset.sum_image]
  intro p _ q _ he
  exact replacement_injective pre tail he

theorem frozen_correction_eq_original (Y : ℕ) (w top R theta : ℝ)
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (mu : ℝ) (r : ℚ) (pre tail : List ℕ) (htail : tail ≠ [])
    (hWords : ∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
      (pre++p::tail).Pairwise (· > ·) ∧ ∀ q ∈ pre++p::tail,q ∈ sourcePrimeSet w top) :
    (∑ ps ∈ frozenGroup R theta (fun t => (a t : ℤ)) r pre tail,
      (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a
        (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
       referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)))=
    ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
      ((modulusCount Y (ErdosStoppedTagSieve.smallPrimeSet (tail.getLastD 0 : ℝ)) a
        (p*(pre.prod*tail.prod)) : ℝ)-
       referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (pre++p::tail))) := by
  rw [frozen_group_reward_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [strict_smallPrimeSet_nat]
  rw [frozen_survivors_eq_modulusCount Y hw htop a z mu pre tail p htail
    (hWords p hp).1 (hWords p hp).2]

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.CanonicalKeyWitness NumberTheoryLean.CanonicalKeyReplacement
  NumberTheoryLean.CanonicalStopKey NumberTheoryLean.SourceStopPredicate
  NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition
  ErdosInverseAlignment ErdosInversePrimeBin ErdosStoppedTagSieve ErdosHypotheticalTag


theorem canonical_key_arithmetic (Cs : ℝ) : ∀ᶠ w : ℝ in atTop,
    ∀ top xi : ℝ,∀ hw : 1 < w,∀ htop : w < top,∀ hxi : 0 < xi,
    ∀ Y : ℕ,∀ eta Clen B b₀ b₁ mu : ℝ,∀ a : ℕ → ℕ,∀ z : Node,
    ∀ k : Key (binCount w top xi),Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k →
      (k.tail.getLastD 0).Prime ∧ 0 < k.pre.prod*k.tail.prod ∧
      (∀ t ∈ smallPrimeSet (k.tail.getLastD 0 : ℝ),(k.pre.prod*k.tail.prod).Coprime t) ∧
      ∀ p ∈ primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
        Squarefree (p*(k.pre.prod*k.tail.prod)) ∧ k.tag.rational.den.Coprime p ∧
        p ∉ smallPrimeSet (k.tail.getLastD 0 : ℝ) ∧
        (∀ t ∈ (p*(k.pre.prod*k.tail.prod)).primeFactors,t ≠ p →
          aligns (sourceClass a) k.tag.rational t) ∧
        ∀ t ∈ (p*(k.pre.prod*k.tail.prod)).primeFactors,k.tail.getLastD 0 ≤ t := by
  filter_upwards [source_all_search_units Cs] with w hUnits
  intro top xi hw htop hxi Y eta Clen B b₀ b₁ mu a z k d
  have hFixed := fixed_other_alignment hw htop hxi d
  have hPrime0 : ∀ p ∈ k.pre++d.p₀::k.tail,p.Prime := by
    intro p hp
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (d.source p hp)).1
  obtain ⟨hP,hq,_hsq0,_hSupport0,_hSmall0,hqCoprime,_hOther0⟩ :=
    fixed_tail_arithmetic k.pre k.tail d.p₀ d.tail_nonempty d.ordered hPrime0 (sourceClass a) k.tag.rational hFixed
  refine ⟨hP,hq,hqCoprime,?_⟩
  intro p hp
  have hWord := whole_bin_words hw htop hxi d p hp
  have hPrime : ∀ t ∈ k.pre++p::k.tail,t.Prime := by
    intro t ht
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop t).mp (hWord.2 t ht)).1
  obtain ⟨_hP,_hq,hsq,hSupport,hSmall,_hqCo,hOther⟩ :=
    fixed_tail_arithmetic k.pre k.tail p d.tail_nonempty hWord.1 hPrime (sourceClass a) k.tag.rational hFixed
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have hWidth : 0 ≤ width w top xi k.tag.bin := (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hpBounds := (mem_primeBin hR.le hWidth p).mp hp
  have hUnit := hUnits.2 (lower w top xi k.tag.bin) k.tag.rational p hR d.eligible.1
    d.search hpBounds.2.1.le hpBounds.1
  exact ⟨hsq,hUnit,hSmall,hOther,hSupport⟩

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.CanonicalKeyWitness NumberTheoryLean.CanonicalKeyReplacement
  NumberTheoryLean.CanonicalStopKey NumberTheoryLean.ActualStopGroupFiber
  NumberTheoryLean.SourceStopPredicate NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.StoppedVertexHistory
  NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion
  NumberTheoryLean.ReferenceProductsBasics
  ErdosInverseAlignment ErdosInversePrimeBin ErdosStoppedTagSieve
  ErdosPrimeInputs.MertensStrong
open ErdosCommonMInterval (lengthExponent)

attribute [local instance] Classical.propDecidable

theorem canonical_key_correction_nonnegative :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
      ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → ∀ hxi : 0 < xi,
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ top : ℝ,
      ∀ hw : 1 < w,∀ htop : w < top,∀ Y : ℕ,0 < Y →
      ∀ eta Clen B b₀ b₁ mu : ℝ,0 ≤ eta → eta ≤ eta0 →
      ∀ a : ℕ → ℕ,∀ z : Node,∀ k : Key (binCount w top xi),
      Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k →
      let P := k.tail.getLastD 0
      let R := lower w top xi k.tag.bin
      let theta := width w top xi k.tag.bin
      let q := k.pre.prod*k.tail.prod
      P0 ≤ P → Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) →
      (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) → xi/4 ≤ theta → theta ≤ 1 →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ p ∈ (primeBin R theta).filter (aligns (sourceClass a) k.tag.rational),
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail)) ≤
          (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
      0 ≤ ∑ ps ∈ keyGroup w top xi a k,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
          referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)) := by
  obtain ⟨eta0,heta0,heta01,P0,hP0,hOwner⟩ := actual_owner_local_comparison_jb247
  refine ⟨eta0,heta0,heta01,P0,hP0,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hOwner⟩ := hOwner Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wA,hwA,hA⟩ := hOwner rho xi hrho hxi
  obtain ⟨wU,hU⟩ := eventually_atTop.mp (canonical_key_arithmetic Cs)
  refine ⟨max wA wU,hwA.trans (le_max_left _ _),?_⟩
  intro w hw top hw1 htop Y hY eta Clen B b₀ b₁ mu heta hetaU a z k d
  dsimp only
  intro hPsize hPl hPu hWidthLo hWidthHi hBand hRef
  obtain ⟨hPrime,hq,hqSmall,hGeometry⟩ :=
    hU w ((le_max_right _ _).trans hw) top xi hw1 htop hxi Y eta Clen B b₀ b₁ mu a z k d
  let ref : ℕ → ℝ := fun p =>
    referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail))
  have hNum : |(k.tag.rational.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using d.eligible.2
  have hMargin := hA w ((le_max_left _ _).trans hw) (k.tail.getLastD 0) hPrime hPsize
    (lower w top xi k.tag.bin) (width w top xi k.tag.bin) eta hPl hPu
    (search_lower hw1 htop hxi d) hWidthLo hWidthHi heta hetaU Y (k.pre.prod*k.tail.prod)
    hY hq k.tag.rational a d.eligible.1 hNum hBand hqSmall hGeometry d.near_full ref hRef
  have hNonneg : 0 ≤ (1/100 : ℝ)*primeProduct (k.tail.getLastD 0 : ℝ)*
      (∑ p ∈ primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
        (Y : ℝ)/((p : ℝ)*(k.pre.prod*k.tail.prod : ℕ))) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (actual_primeProduct_pos _).le)
    exact Finset.sum_nonneg (fun p _ => by positivity)
  change 0 ≤ ∑ ps ∈ NumberTheoryLean.FrozenPrimeGroup.frozenGroup
    (lower w top xi k.tag.bin) (width w top xi k.tag.bin) (fun t => (a t : ℤ)) k.tag.rational k.pre k.tail,_
  rw [frozen_correction_eq_original Y w top (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
    (zero_lt_one.trans hw1) htop a z mu k.tag.rational k.pre k.tail d.tail_nonempty
    (fun p hp => whole_bin_words hw1 htop hxi d p (Finset.mem_filter.mp hp).1)]
  exact hNonneg.trans hMargin

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open NumberTheoryLean NumberTheoryLean.PrimeHistories NumberTheoryLean.CanonicalStopPartition
  NumberTheoryLean.ActualStopGroupFiber NumberTheoryLean.SourceStopPredicate
  NumberTheoryLean.StoppedCountVertex NumberTheoryLean.StoppedCountAdapters
  NumberTheoryLean.StoppedVertexHistory NumberTheoryLean.StoppedTraceSets
  NumberTheoryLean.LogarithmicBinEndpoints NumberTheoryLean.LogarithmicBinLabels
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion


theorem stopped_correction_of_key_signs (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node)
    (hKeys : ∀ k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
      0 ≤ ∑ ps ∈ keyGroup w top xi a k,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
          referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps))) :
    0 ≤ ∑ ps ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu),
      (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)) := by
  change 0 ≤ ∑ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,_
  rw [sum_over_groups Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z]
  exact Finset.sum_nonneg hKeys

end ErdosStoppedArithmetic


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

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale NumberTheoryLean.PrimeBinMembership

theorem rootW_tendsto : Tendsto ErdosInverseBoxHeight.sourceW atTop atTop := by
  exact sourceW_tendsto.comp Real.tendsto_log_atTop

theorem rootB_tendsto : Tendsto ErdosInverseBoxHeight.sourceB atTop atTop := by
  exact sourceB_tendsto.comp Real.tendsto_log_atTop

theorem actual_root_eventually (a : ℝ) : ∀ᶠ z : ℝ in atTop,
    0 < ErdosInverseBoxHeight.sourceB z ∧ 1 < ErdosInverseBoxHeight.sourceW z ∧
    Real.log (ErdosInverseBoxHeight.sourceB z) ≤ 2*Real.log (ErdosInverseBoxHeight.sourceW z) ∧
    199/100 ≤ (sourceRootNode a z).ratio ∧ (sourceRootNode a z).ratio ≤ 23/10 ∧
    0 < (sourceRootNode a z).gap ∧ Consistent (sourceRootNode a z) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (paper_start_eventually a true floorRemainder_tendsto),
    Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hp hs hz
  simp only [sourceRoot_eq_paper a hz hs.1]
  exact hp

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRootReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceRootReference
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourceDecomposition ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceAdmission
open LogarithmicBinPartition SourceNodeCoordinates
open ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosInverseBoxHeight
open scoped Topology


theorem source_root_eventually_data : ∀ᶠ top : ℝ in atTop,
    0 < sourceY top ∧ 3 ≤ sourceB top ∧ 1 < sourceW top ∧ sourceW top < top ∧
    Real.log (sourceB top) ≤ 2*Real.log (sourceW top) ∧
    199/100 ≤ (sourceRootNode (1/100) top).ratio ∧ (sourceRootNode (1/100) top).ratio ≤ 23/10 ∧
    Consistent (sourceRootNode (1/100) top) ∧ (sourceW top)^(sourceB top)=top := by
  filter_upwards [actual_root_eventually (1/100),rootB_tendsto.eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ)]
    with top hroot hB hW ht1
  obtain ⟨_hBpos,hw,hcomp,h199,h23,_hgap,hcons⟩ := hroot
  have hwt : sourceW top < top := by
    have hsmall : sourceW top ≤ Real.log top := hW.2.2
    have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht1)
    linarith
  have hY : 0 < sourceY top := by
    by_contra! hn
    have hzero : sourceY top=0 := by omega
    have hg : (sourceRootNode (1/100) top).gap=199/100 := by
      change Real.log (sourceY top:ℝ)/Real.log (sourceW top)-(1:ℝ)/100+2=199/100
      rw [hzero]
      norm_num
    have hs : Valid (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).ratio := by
      change 198/100 ≤ (sourceRootNode (1/100) top).ratio
      linarith
    have he := node_gap_eq hs hcons (rfl : (sourceRootNode (1/100) top).cutoff=sourceB top)
    change (sourceRootNode (1/100) top).gap=sourceB top*(sourceRootNode (1/100) top).ratio at he
    have hprod := mul_le_mul h199 hB (by norm_num : (0:ℝ)≤3) (by linarith : 0 ≤ (sourceRootNode (1/100) top).ratio)
    nlinarith
  exact ⟨hY,hB,hw,hwt,hcomp,h199,h23,hcons,
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans ht1))⟩
end NumberTheoryLean.SourceRootReference


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceCanonicalKeyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceCanonicalKeyGeometry
open _root_.Filter PrimeHistories CanonicalStopKey CanonicalStopPartition CanonicalKeyWitness
open CanonicalKeyBands CanonicalKeyReference SourceRootReference
open StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.MertensStrong
open ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem source_key_geometry {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (hrho : 0 < rho) (P0 : ℕ) :
    ∀ᶠ top : ℝ in atTop,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let z := sourceRootNode (1/100) top
      let mu := (Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊
      0 < Y ∧ ∃ hw : 1 < w,∃ htop : w < top,∀ Cs eta : ℝ,∀ a : ℕ → ℕ,
      ∀ k∈keys Y w top Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        mu hw htop hxi a z,
      Nonempty (Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2)
        (rho*Kstop*(Real.log w)^2) mu a z k) ∧
      P0 ≤ k.tail.getLastD 0 ∧
      Real.exp ((Kstop/2)*(Real.log w)^3) ≤ (k.tail.getLastD 0:ℝ) ∧
      (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) ∧
      xi/4 ≤ width w top xi k.tag.bin ∧ width w top xi k.tag.bin ≤ 1 ∧
      (∀ p∈Set.Icc (lower w top xi k.tag.bin) ((1+width w top xi k.tag.bin)*lower w top xi k.tag.bin),
        203/100 ≤ Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ≤ 219/100) ∧
      (∀ p∈(primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).filter
          (aligns (SourceStopPredicate.sourceClass a) k.tag.rational),
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail))
          ≤ (33/100)*primeProduct (k.tail.getLastD 0:ℝ)*
            ((Y:ℝ)/((p:ℝ)*(k.pre.prod*k.tail.prod:ℕ)))) := by
  filter_upwards [source_root_eventually_data,ErdosCofactorChoices.source_span_geometry,
    rootW_tendsto.eventually (moving_key_bands hC hxi hxi1 hK hrho),
    rootW_tendsto.eventually (moving_key_reference_jb247 hC hxi hxi1 hK hrho),
    rootW_tendsto.eventually (TagBelowStopWindow.moving_window_below_search rho Kstop hrho hK),
    rootW_tendsto.eventually_ge_atTop (P0:ℝ)] with top hData hSpan hBands hRef hWindow hP0
  dsimp only
  obtain ⟨hY,_hB,hw,htop,hcomp,_hrlo,_hrhi,_hcons,_hpower⟩ := hData
  obtain ⟨_hwB,hBands⟩ := hBands
  obtain ⟨_hwR,hRef⟩ := hRef
  refine ⟨hY,hw,htop,?_⟩
  intro Cs eta a k hk
  obtain ⟨d⟩ := key_witness_exists hw htop hxi (sourceY top) Cs eta Clen (sourceB top)
    (Kstop*(Real.log (sourceW top))^2) (rho*Kstop*(Real.log (sourceW top))^2)
    ((sourceY top:ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) a
    (sourceRootNode (1/100) top) hWindow k hk
  have hBand := hBands top htop (sourceB top) hcomp (sourceY top) hY (1/100) Cs eta
    ((sourceY top:ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (by norm_num) (by norm_num)
    a (sourceRootNode (1/100) top) rfl k d
  have hTail : k.tail.getLastD 0∈k.tail := by
    have he : k.tail.getLastD 0=k.tail.getLast d.tail_nonempty := by
      conv_lhs => rw [← List.dropLast_append_getLast d.tail_nonempty]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem d.tail_nonempty
  have hPsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop (k.tail.getLastD 0)).mp
    (d.source _ (by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr hTail)))
  have hPsize : P0 ≤ k.tail.getLastD 0 := by exact_mod_cast hP0.trans hPsource.2.1.le
  refine ⟨⟨d⟩,hPsize,hBand.1,hBand.2.1,?_,?_,hBand.2.2,?_⟩
  · exact effectiveWidth_ge_quarter (zero_lt_one.trans hw) htop hxi hxi1 (hSpan.2.2 xi hxi hxi1)
  · exact (effectiveWidth_le (zero_lt_one.trans hw) htop hxi).trans hxi1
  · intro p hp
    exact hRef top htop (sourceB top) hcomp (sourceY top) Cs eta a (sourceRootNode (1/100) top) k d
      p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
end NumberTheoryLean.SourceCanonicalKeyGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SourceStoppedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final
open _root_.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.SourceCanonicalKeyGeometry NumberTheoryLean.CanonicalStopPartition
  NumberTheoryLean.SourceStopPredicate NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.StoppedVertexHistory
  NumberTheoryLean.StoppedTraceSets NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinLabels NumberTheoryLean.LogarithmicBinPartition
  NumberTheoryLean.LargePrimeDeletion
  ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosStoppedArithmetic

attribute [local instance] Classical.propDecidable

theorem source_stopped_correction :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∀ Cs : ℝ,0 ≤ Cs →
      ∃ K : ℝ,0 < K ∧ ∀ Clen : ℝ,0 ≤ Clen → ∀ eta : ℝ,0 ≤ eta → eta ≤ eta0 →
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∀ rho : ℝ,1 < rho →
      ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ a : ℕ → ℕ,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let mu := (Y : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊
      let z := sourceRootNode (1/100) top
      let P := sourcePrimeSet w top
      let v := rootVertex z ∅ P mu
      let stop := stopCandidate Y w Cs eta Clen B xi ((2*K)*(Real.log w)^2)
        (rho*(2*K)*(Real.log w)^2) (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z
      0 ≤ ∑ ps ∈ stopped w stop P.card v,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w v ps)-referenceValue w (after w v ps)) := by
  obtain ⟨eta0,heta0,heta01,P0,_hP0,hArithmetic⟩ := canonical_key_correction_nonnegative
  refine ⟨eta0,heta0,heta01,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hArithmetic⟩ := hArithmetic Cs hCs
  refine ⟨K,hK,?_⟩
  intro Clen hClen eta heta hetaU xi hxi hxi1 rho hrho
  have hKstop : 0 < 2*K := by positivity
  obtain ⟨W,_hW,hArithmetic⟩ := hArithmetic (2*rho) xi (by linarith) hxi
  have hGeometry := source_key_geometry hClen hxi hxi1 hKstop (by linarith : 0 < rho) P0
  filter_upwards [hGeometry,rootW_tendsto.eventually_ge_atTop W] with top hGeometry hW
  dsimp only at hGeometry
  obtain ⟨hY,hw,htop,hGeometry⟩ := hGeometry
  refine ⟨hw,htop,?_⟩
  intro a
  dsimp only
  apply stopped_correction_of_key_signs (sourceY top) (sourceW top) top Cs eta Clen
    (sourceB top) xi ((2*K)*(Real.log (sourceW top))^2) (rho*(2*K)*(Real.log (sourceW top))^2)
    ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) hw htop hxi hClen a
    (sourceRootNode (1/100) top)
  intro k hk
  obtain ⟨⟨d⟩,hPsize,hPl,hPu,hWidthLo,hWidthHi,hBand,hRef⟩ := hGeometry Cs eta a k hk
  have hPl' : Real.exp (K*(Real.log (sourceW top))^3) ≤ (k.tail.getLastD 0 : ℝ) := by
    simpa only [show (2*K)/2=K by ring] using hPl
  have hPu' : (k.tail.getLastD 0 : ℝ) ≤ Real.exp ((2*rho)*K*(Real.log (sourceW top))^3) := by
    convert hPu using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  apply hArithmetic (sourceW top) hW top hw htop (sourceY top) hY eta Clen (sourceB top)
    ((2*K)*(Real.log (sourceW top))^2) (rho*(2*K)*(Real.log (sourceW top))^2)
    ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) heta hetaU a
    (sourceRootNode (1/100) top) k d hPsize hPl' hPu' hWidthLo hWidthHi
  · simpa only [ErdosCommonMInterval.lengthExponent,ErdosCommonMInterval.referenceLength] using hBand
  · exact hRef

end Erdos970Final


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_SourceRootCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Final
open _root_.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.SourceRootErrorLower NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.LogarithmicBinPartition
  NumberTheoryLean.LargePrimeDeletion
  ErdosInverseBoxHeight ErdosCorrectionLimit


theorem source_root_survivor_lower : ∃ c : ℝ,0 < c ∧ ∀ᶠ top : ℝ in atTop,
    ∀ a : ℕ → ℕ,
    c*((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊/(sourceB top)^2) ≤
      countSurvivors (sourceY top) (cutoffPrimes ⌊sourceW top⌋₊) a
        (rootVertex (sourceRootNode (1/100) top) ∅ (sourcePrimeSet (sourceW top) top)
          ((sourceY top : ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)) := by
  obtain ⟨eta0,heta0,heta01,hCorrection⟩ := source_stopped_correction
  obtain ⟨c,Clen,Cs,xi0,hc,hClen,hCs,_hCsMin,hxi0,hxi01,hError⟩ :=
    source_root_lower_with_stopped_correction_jb247 1
  have hClenPos : 0 < Clen := by linarith
  obtain ⟨K,hK,hCorrection⟩ := hCorrection Cs hCs.le
  let eta : ℝ := eta0/2
  let xi : ℝ := min (xi0/2) (1/(40*Clen))
  have heta : 0 < eta := by dsimp [eta] <;> positivity
  have hetaU : eta ≤ eta0 := by dsimp [eta] <;> linarith
  have hetaHalf : eta < 1/2 := by dsimp [eta] <;> linarith
  have hxi : 0 < xi := lt_min (by positivity) (by positivity)
  have hxiU : xi ≤ xi0 := (min_le_left _ _).trans (by linarith)
  have hxi1 : xi ≤ 1 := hxiU.trans hxi01
  obtain ⟨rho,hrho,hError⟩ := hError eta heta hetaHalf xi hxi hxiU
  have hKstop : 0 < 2*K := by positivity
  have hCorrection := hCorrection Clen hClenPos.le eta heta.le hetaU xi hxi hxi1 rho (by linarith)
  refine ⟨c,hc,?_⟩
  filter_upwards [hError (2*K) hKstop,hCorrection] with top hError hCorrection
  obtain ⟨_hw,_htop,hError⟩ := hError
  obtain ⟨_hwC,_htopC,hCorrection⟩ := hCorrection
  intro a
  have hLower := hError a
  have hSign := hCorrection a
  dsimp only at hLower hSign
  linarith

end Erdos970Final


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_IteratedLogBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970.Erdos970Final

/-- Manuscript 293, strengthened Theorem 1.1, revision ad16712e7b45. -/
theorem erdos_970_iterated_log_oai : NumberTheoryLean.Targets.JacobsthalIteratedLog := by
  obtain ⟨c, hc, hLower⟩ := source_root_survivor_lower
  exact NumberTheoryLean.IteratedLogBound.of_source_root_lower_jb247 c hc
    (ErdosCorrectionLimit.sourceRootNode (1 / 100)) hLower

end Erdos970.Erdos970Final

end OAI
end

theorem solution : type_of% @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log_oai := @OAI.Erdos970.Erdos970Final.erdos_970_iterated_log_oai
