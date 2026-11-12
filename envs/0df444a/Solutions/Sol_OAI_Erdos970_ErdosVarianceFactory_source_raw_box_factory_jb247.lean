-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:23.635124+00:00
-- url     : https://prove2.me/submissions/c34d9257-a2d6-4fa7-9bb9-d78eb3870907

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
import Theorems.Thm_OAI_Erdos970_ErdosVarianceEligible_geometric_selection_recent_witness_jb247
import Theorems.Thm_OAI_Erdos970_ErdosVarianceWeighted_source_selection_hard_mass_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_GeometricRangeCandidateUnion_geometric_range_candidate_union_jb247

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

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

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

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedCofactorSplit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem badPrimeProduct_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : 0 < badPrimeProduct a r qf :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem alignedPrimeProduct_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : 0 < alignedPrimeProduct a r qf :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem aligned_bad_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedPrimeProduct a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedPrimeProduct,alignedPrimeFactors,badPrimeProduct,badPrimeFactors,
    Finset.prod_filter_mul_prod_filter_not,Nat.prod_primeFactors_of_squarefree hq]

theorem alignedCofactor_eq_product (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf = alignedPrimeProduct a r qf := by
  unfold alignedCofactor
  nth_rw 1 [← aligned_bad_product a r qf hq]
  exact Nat.mul_div_cancel _ (badPrimeProduct_pos a r qf)

theorem alignedCofactor_pos (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    0 < alignedCofactor a r qf := by
  rw [alignedCofactor_eq_product a r qf hq]
  exact alignedPrimeProduct_pos a r qf

theorem alignedCofactor_mul_bad (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor a r qf*badPrimeProduct a r qf = qf := by
  rw [alignedCofactor_eq_product a r qf hq]
  exact aligned_bad_product a r qf hq

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveNumerator
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem prime_dvd_hitNumerator_iff (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p ∈ qf.primeFactors) :
    (p : ℤ) ∣ hitNumerator a r qf ↔ aligns (fun t => (a t : ℤ)) r p := by
  have hclass : (cofactorHit qf a : ZMod p) = (a p : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((cofactorHit_spec qf hq a).2.2 p hp)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hclass,sub_eq_zero,aligns]

theorem alignedCofactor_dvd_hitNumerator (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ) ∣ hitNumerator a r qf := by
  apply Int.natCast_dvd.mpr
  rw [alignedCofactor_eq_product _ r qf hq]
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf,halign⟩ := Finset.mem_filter.mp hp
    exact Int.natCast_dvd.mp ((prime_dvd_hitNumerator_iff a r qf hq p hpf).mpr halign)

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EffectiveCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

theorem effectiveModulus_pos (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : 0 < effectiveModulus a r qf :=
  Nat.mul_pos r.pos (badPrimeProduct_pos _ r qf)

theorem effectiveIntercept_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*effectiveIntercept a r qf = hitNumerator a r qf := by
  rw [effectiveIntercept,mul_comm]
  exact Int.ediv_mul_cancel (alignedCofactor_dvd_hitNumerator a r qf hq)

theorem denominator_full_cofactor (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    r.den*qf = alignedCofactor (fun t => (a t : ℤ)) r qf*effectiveModulus a r qf := by
  calc
    _ = r.den*(alignedCofactor (fun t => (a t : ℤ)) r qf*badPrimeProduct (fun t => (a t : ℤ)) r qf) :=
      congrArg (fun x : ℕ => r.den*x) (alignedCofactor_mul_bad (fun t => (a t : ℤ)) r qf hq).symm
    _ = _ := by unfold effectiveModulus;ring

end ErdosVarianceEffective

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

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem badPrimeProduct_extension_dvd (a : ℕ → ℤ) (r : ℚ) (q e : ℕ) (hq : q ≠ 0) :
    badPrimeProduct a r (q*e) ∣ badPrimeProduct a r q*e := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf,hnon⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hpf
    rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hpf) with hpq | hpe
    · have hpbad : p ∈ badPrimeFactors a r q := Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hprime,hpq,hq⟩,hnon⟩
      exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpbad) e
    · exact dvd_mul_of_dvd_right hpe _

theorem effectiveModulus_extension_le (a : ℕ → ℕ) (r : ℚ) (q e : ℕ) (hq : 0 < q) (he : 0 < e) :
    effectiveModulus a r (q*e) ≤
      (r.den*badPrimeProduct (fun t => (a t : ℤ)) r q)*e := by
  have hh := Nat.le_of_dvd (Nat.mul_pos (badPrimeProduct_pos (fun t => (a t : ℤ)) r q) he)
    (badPrimeProduct_extension_dvd (fun t => (a t : ℤ)) r q e hq.ne')
  simpa only [effectiveModulus,Nat.mul_assoc] using Nat.mul_le_mul_left r.den hh

theorem effectiveModulus_height_of_extension (a : ℕ → ℕ) (r : ℚ) (q e : ℕ) (hq : 0 < q) (he : 0 < e)
    (R Z : ℝ) (hR : 0 ≤ R) (_hZ : 0 ≤ Z)
    (hparent : ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ) ≤ R*Z^10)
    (heZ : (e : ℝ) ≤ Z) :
    (effectiveModulus a r (q*e) : ℝ) ≤ R*Z^11 := by
  calc
    _ ≤ ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ)*(e : ℝ) := by
      exact_mod_cast effectiveModulus_extension_le a r q e hq he
    _ ≤ (R*Z^10)*Z := mul_le_mul hparent heZ (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end ErdosVarianceEffective

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceEffective
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost

theorem sourceW_power_subpower (A eps : ℝ) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,(sourceW z)^A ≤ (sourceZ z)^eps := by
  filter_upwards [sourceW_log_bounds,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    exp_loglog_sq_le_sourceZ A eps hA heps] with z hz hLL hExp
  have hW : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  change 1 ≤ Real.log (Real.log z) at hLL
  have hLLsq : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith
  calc
    _ ≤ (Real.log z)^A := Real.rpow_le_rpow hW.le hz.2.2.2 hA
    _ = Real.exp (A*Real.log (Real.log z)) := by rw [Real.rpow_def_of_pos hz.2.1];congr 1;ring
    _ ≤ Real.exp (A*(Real.log (Real.log z))^2) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hLLsq hA)
    _ ≤ _ := hExp

theorem extension_le_parent_power (Y p q e : ℕ) (hp : 0 < p) (hq : 0 < q) (he : 0 < e)
    (w C : ℝ) (hw : 1 < w) (hFinal : p*(q*e) ≤ Y)
    (hParent : Real.logb w ((Y : ℝ)/((p : ℝ)*q)) ≤ C) : (e : ℝ) ≤ w^C := by
  have hden : 0 < (p : ℝ)*q := by positivity
  have hY : 0 < Y := (Nat.mul_pos hp (Nat.mul_pos hq he)).trans_le hFinal
  have hratio : 0 < (Y : ℝ)/((p : ℝ)*q) := by positivity
  have hbound : (e : ℝ) ≤ (Y : ℝ)/((p : ℝ)*q) := by
    apply (le_div_iff₀ hden).mpr
    have hh : (p : ℝ)*((q : ℝ)*(e : ℝ)) ≤ (Y : ℝ) := by exact_mod_cast hFinal
    nlinarith
  exact hbound.trans ((Real.logb_le_iff_le_rpow hw hratio).mp hParent)

theorem source_extension_le_Z (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop,∀ p q e : ℕ,0 < p → 0 < q → 0 < e →
      p*(q*e) ≤ sourceY z →
      Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ C → (e : ℝ) ≤ sourceZ z := by
  filter_upwards [sourceW_power_subpower C 1 hC zero_lt_one,sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hpower hW
  intro p q e hp hq he hFinal hParent
  have hh := extension_le_parent_power (sourceY z) p q e hp hq he (sourceW z) C (by linarith) hFinal hParent
  exact hh.trans (by simpa only [Real.rpow_one] using hpower)

end ErdosVarianceEffective

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

end ErdosInverseRefinement

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

end NumberTheoryLean.SingletonBinProduct



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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawBoxRationalWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.StructuredWitnessOutside
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts ErdosInverseBoxApplication ErdosInverseSampleCost
open ErdosInverseAlignment ErdosInverseStructured ErdosPrimitiveIntercept
open PrimeHistories TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices SingletonBinSelection BinCutSelections
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem full_selection_coordinates {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hi : m i=1) (hj : m j=1) :
    pickedPrime f i ∈ P i ∧ pickedPrime f j ∈ P j ∧
      selectionProduct (parentCofactorSelection f i j) ∈ cofactorChoices P (parentCofactorMultiplicity m i j) := by
  obtain ⟨p,hp,hfi,_⟩ := singleton_selection_recovery P m i hi f hf
  obtain ⟨u,hu,hfj,_⟩ := singleton_selection_recovery P m j hj f hf
  refine ⟨by simpa [pickedPrime,hfi] using hp,by simpa [pickedPrime,hfj] using hu,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨parentCofactorSelection f i j,?_,rfl⟩
  exact erase_selection_mem P (aboveMultiplicity m j) (aboveSelection f j) (above_selection_mem P m f hf j) i

theorem structured_full_selection {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hi : m i=1) (hj : m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 S R Z cp sigma : ℝ) (F : ℕ)
    (hInv : SourceInverseConclusion Y small a delta V0 S R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j))
    (hbad : WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j))
    (hout : ¬actualWitness Y small a delta V0 (P i) S R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) :
    ∃ t ∈ sourceRationalList (P i) (fun p => (a p:ℤ)) S R Z cp,
      aligns (fun p => (a p:ℤ)) t (pickedPrime f i) ∧
      ((t.den*badPrimeProduct (fun p => (a p:ℤ)) t (selectionProduct (parentCofactorSelection f i j)):ℕ):ℝ) ≤ R*Z^10 := by
  have hc := full_selection_coordinates P m f hf i j hi hj
  have hnot : ((pickedPrime f i,selectionProduct (parentCofactorSelection f i j)),pickedPrime f j) ∉
      actualInverseException Y small a delta V0 S R Z cp (P i)
        (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) := by
    intro he
    have hh := (mem_actualInverseException Y small a delta V0 S R Z cp _ _ _ _ _ _).mp he
    exact hout ⟨hh.2.2.2.1,hh.2.2.2.2⟩
  exact hInv.2.2.2 _ hc.1 _ hc.2.2 _ hc.2.1 hnot hbad
end NumberTheoryLean.StructuredWitnessOutside



namespace NumberTheoryLean.RawBoxRationalWitness
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts ErdosInverseBoxApplication ErdosInverseSampleCost
open ErdosInverseAlignment ErdosInverseStructured ErdosPrimitiveIntercept
open StructuredWitnessOutside TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices

attribute [local instance] Classical.propDecidable

theorem raw_box_list_card {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (J : Finset (Fin n))
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (S : Fin n → ℝ) (R Z cp sigma : ℝ) (F : ℕ)
    (hInv : ∀ j∈J,SourceInverseConclusion Y small a delta V0 (S j) R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j)) :
    (rawBoxList P i J a S R Z cp).card ≤ J.card*F := by
  have hh := (Finset.card_biUnion_le : (rawBoxList P i J a S R Z cp).card ≤
    ∑ j∈J,(sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp).card)
  exact hh.trans ((Finset.sum_le_sum (fun j hj => (hInv j hj).1)).trans_eq (by simp))

theorem raw_box_witness {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (J : Finset (Fin n))
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (hi : m i=1) (hj : ∀ j∈J,m j=1)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (S : Fin n → ℝ) (R Z cp sigma : ℝ) (F : ℕ)
    (hInv : ∀ j∈J,SourceInverseConclusion Y small a delta V0 (S j) R Z cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j))
    (hbad : ∃ j∈J,WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j))
    (hout : ¬∃ j∈J,actualWitness Y small a delta V0 (P i) (S j) R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) :
    ∃ j∈J,∃ t∈rawBoxList P i J a S R Z cp,
      t ∈ sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp ∧
      aligns (fun p => (a p:ℤ)) t (pickedPrime f i) ∧
      ((t.den*badPrimeProduct (fun p => (a p:ℤ)) t (selectionProduct (parentCofactorSelection f i j)):ℕ):ℝ) ≤ R*Z^10 := by
  obtain ⟨j,hjJ,hb⟩ := hbad
  have hno : ¬actualWitness Y small a delta V0 (P i) (S j) R Z cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) :=
    fun h => hout ⟨j,hjJ,h⟩
  obtain ⟨t,ht,ha,hd⟩ := structured_full_selection P m f hf i j hi (hj j hjJ) Y small a delta V0 (S j) R Z cp sigma F
    (hInv j hjJ) hb hno
  exact ⟨j,hjJ,t,Finset.mem_biUnion.mpr ⟨j,hjJ,ht⟩,ht,ha,hd⟩
end NumberTheoryLean.RawBoxRationalWitness


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ErasedCofactorGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection ErdosInverseRefinement
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem erased_cofactor_arithmetic {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i : Fin (binCount w top xi))
    (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (eraseMultiplicity m i)) :
    Squarefree (selectionProduct f) ∧ (∀ t ∈ (selectionProduct f).primeFactors,w < (t : ℝ)) ∧
      ∀ p ∈ globalBins w top xi i,(selectionProduct f).Coprime p := by
  let P := globalBins w top xi
  have hP : ∀ j,∀ p ∈ P j,p.Prime := fun j p hp => (bin_prime_in_source (by linarith) htop hxi j hp).1
  have hd : Pairwise (fun j k => Disjoint (P j) (P k)) :=
    fun j k hjk => bins_pairwise_disjoint (by linarith) htop hxi j k hjk
  have hq : selectionProduct f ∈ cofactorChoices P (eraseMultiplicity m i) :=
    Finset.mem_image.mpr ⟨f,hf,rfl⟩
  refine ⟨cofactor_squarefree P _ hP hd _ hq,?_,
    cofactor_coprime_excluded_bin P _ hP hd i (by simp [eraseMultiplicity]) _ hq⟩
  intro t ht
  rw [selectionProduct_primeFactors P hP hd f (fun j => ((mem_selections P _ f).mp hf j).1)] at ht
  obtain ⟨j,_hj,htj⟩ := Finset.mem_biUnion.mp ht
  exact (bin_prime_in_source (by linarith) htop hxi j (((mem_selections P _ f).mp hf j).1 htj)).2.1

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FullBoxTotalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  StrongSourceFamilies SafeSubsetBoxGeometry ActualReferencePrefixes PrimeProductLogCoordinates
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection SingletonBinProduct
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
attribute [local instance] Classical.propDecidable

theorem full_box_total_length_lower {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m) :
    a ≤ Real.log ((Y : ℝ)/(selectionProduct f : ℝ))/Real.log w := by
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hprefix : descendingWord f ∈ (descendingWord f).inits :=
    (List.mem_inits _ _).mpr ⟨[],by simp⟩
  have hgap := reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap _ _ hfull hprefix
  have hsource := word_source_membership hw htop hxi m f hf
  have hlog := terminal_gap_log_quotient Y hY z hroot (descendingWord f)
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos)
  have hprod := descendingWord_product (globalBins w top xi)
    (fun j k hjk => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi j k hjk)
    f (fun j => ((mem_selections _ m f).mp hf j).1)
  rw [hprod] at hlog
  linarith

theorem erased_cofactor_all_lengths {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (i : Fin (binCount w top xi)) (hi : m i = 1)
    (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (eraseMultiplicity m i)) :
    ∀ p ∈ globalBins w top xi i,a ≤ Real.log ((Y : ℝ)/((p : ℝ)*selectionProduct f))/Real.log w := by
  intro p hp
  have hfill := fill_selection_mem (globalBins w top xi) m i hi f hf p hp
  have hh := full_box_total_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m ha
    (fillSelection f i p) hfill
  rw [filled_product f i p (erased_coordinate_empty _ m i f hf),Nat.cast_mul] at hh
  exact hh

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FullBoxVarianceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport SafeSubsetBoxGeometry
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection LogarithmicBinScale

theorem product_le_Y_of_length (w a : ℝ) (hw : 1 < w) (ha : 0 ≤ a) (Y d : ℕ)
    (hY : 0 < Y) (hd : 0 < d) (hlen : a ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w) : d ≤ Y := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hh : w^a ≤ (Y : ℝ)/(d : ℝ) := (Real.le_logb_iff_rpow_le hw (div_pos hYR hdR)).mp hlen
  have hratio : 1 ≤ (Y : ℝ)/(d : ℝ) := (Real.one_le_rpow hw.le ha).trans hh
  have hreal := (le_div_iff₀ hdR).mp hratio
  have hdle : (d : ℝ) ≤ Y := by simpa only [one_mul] using hreal
  exact_mod_cast hdle

theorem full_box_variance_fibres {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C) (ha0 : 0 ≤ a)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi C B K z m)
    (i : Fin (binCount w top xi)) (hi : m i = 1) :
    ∀ f ∈ selections (globalBins w top xi) (eraseMultiplicity m i),Squarefree (selectionProduct f) ∧
      (∀ t ∈ (selectionProduct f).primeFactors,w < (t : ℝ)) ∧
      (∀ p ∈ globalBins w top xi i,(selectionProduct f).Coprime p ∧
        3*a/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*selectionProduct f))/Real.log w) := by
  intro f hf
  have harith := erased_cofactor_arithmetic hw htop hxi m i f hf
  have hlen := erased_cofactor_all_lengths hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m hanchor i hi f hf
  refine ⟨harith.1,harith.2.1,?_⟩
  intro p hp
  exact ⟨harith.2.2 p hp,(by linarith : 3*a/4 ≤ a).trans (hlen p hp)⟩

end ErdosVarianceWeighted

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EndpointCofactorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FullIsolatedCofactor
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open SingletonBinSelection SingletonBinProduct TwoPrimeObservableSum
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem isolated_product {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f∈selections P m) (i : Fin n) (hi : m i=1) :
    selectionProduct f=pickedPrime f i*selectionProduct (eraseSelection f i) := by
  obtain ⟨p,_hp,hfi,hfill⟩ := singleton_selection_recovery P m i hi f hf
  have hprod := filled_product (eraseSelection f i) i p (by simp [eraseSelection])
  rw [hfill] at hprod
  simpa [pickedPrime,hfi] using hprod

theorem full_word_isolated_product {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1) :
    (descendingWord f).prod=pickedPrime f i*selectionProduct (eraseSelection f i) := by
  rw [descendingWord_product (globalBins w top xi)
    (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
    f (fun k => ((mem_selections _ _ _).mp hf k).1)]
  exact isolated_product _ m f hf i hi

theorem full_cofactor_alignment_word {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i=1)
    (a : ℕ → ℤ) (q : ℚ)
    (ha : ∀ p∈(pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
      Cs < primeExponent w p → aligns a q p) :
    ∀ p∈descendingWord f,Cs < primeExponent w p → aligns a q p := by
  intro p hp hhigh
  apply ha p _ hhigh
  rw [← isolated_product _ m f hf i hi,
    selectionProduct_primeFactors (globalBins w top xi)
      (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1)
      (fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl)
      f (fun k => ((mem_selections _ _ _).mp hf k).1)]
  obtain ⟨k,hpk⟩ := (mem_descendingWord f p).mp hp
  exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hpk⟩
end NumberTheoryLean.FullIsolatedCofactor



namespace NumberTheoryLean.EndpointCofactorSplit
open ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
open ParentTailPartition ParentCofactorChoices BinCutSelections SelectionWordSplit
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition


theorem endpoint_cofactor_split {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hji : j < i) (hj : m j=1) :
    selectionProduct (eraseSelection f i)=selectionProduct (parentCofactorSelection f i j)*
      (pickedPrime f j*selectionProduct (belowSelection f j)) := by
  obtain ⟨u,_hu,hfu,_hfill⟩ := singleton_selection_recovery _ m j hj f hf
  have hfi : eraseSelection f i j={u} := by simp [eraseSelection,ne_of_lt hji,hfu]
  have hErase := erase_selection_mem _ m f hf i
  have hParent := erase_selection_mem _ _ _ (above_selection_mem _ m f hf j) i
  have hBelow := below_selection_mem _ m f hf j
  have hA : aboveSelection (eraseSelection f i) j=parentCofactorSelection f i j := by
    funext k
    by_cases hki : k=i <;> by_cases hjk : j < k <;>
      simp [aboveSelection,eraseSelection,parentCofactorSelection,hki,hjk]
  have hD : belowSelection (eraseSelection f i) j=belowSelection f j := by
    funext k
    by_cases hki : k=i
    · subst k
      simp [belowSelection,not_lt_of_ge hji.le]
    · simp [belowSelection,eraseSelection,hki]
  have hd : Pairwise (fun k l => Disjoint (globalBins w top xi k) (globalBins w top xi l)) :=
    fun k l hkl => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi k l hkl
  have hword := selected_word_split hw htop hxi _ _ hErase j u hfi
  have hprod := congrArg List.prod hword
  rw [List.prod_append,List.prod_cons,hA,hD] at hprod
  rw [descendingWord_product _ hd _ (fun k => ((mem_selections _ _ _).mp hErase k).1),
    descendingWord_product _ hd (parentCofactorSelection f i j) (fun k => ((mem_selections _ _ _).mp hParent k).1),
    descendingWord_product _ hd _ (fun k => ((mem_selections _ _ _).mp hBelow k).1)] at hprod
  simpa [pickedPrime,hfu] using hprod

theorem endpoint_extra_factor_pos {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f∈selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (hj : m j=1) :
    0 < pickedPrime f j*selectionProduct (belowSelection f j) := by
  obtain ⟨u,hu,hfu,_hfill⟩ := singleton_selection_recovery _ m j hj f hf
  have hp : 0 < pickedPrime f j := by
    simpa [pickedPrime,hfu] using (bin_prime_in_source (zero_lt_one.trans hw) htop hxi j hu).1.pos
  have hd : 0 < selectionProduct (belowSelection f j) := selectionProduct_pos (globalBins w top xi)
    (fun k _p hp => (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1) _
    (fun k => ((mem_selections _ _ _).mp (below_selection_mem _ m f hf j) k).1)
  exact Nat.mul_pos hp hd
end NumberTheoryLean.EndpointCofactorSplit


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FullEndpointData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceEffective
open ErdosInverseCells

theorem effective_ratio_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (R : ℝ) :
    |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) =
      |(hitNumerator a r qf : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := by
  let qa := alignedCofactor (fun t => (a t : ℤ)) r qf
  have hqa : (0 : ℝ) < qa := by exact_mod_cast alignedCofactor_pos _ r qf hq
  have he : (qa : ℝ)*(effectiveIntercept a r qf : ℝ) = (hitNumerator a r qf : ℝ) := by
    exact_mod_cast effectiveIntercept_identity a r qf hq
  have hnum : |(hitNumerator a r qf : ℝ)| = (qa : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
    rw [← he,abs_mul,abs_of_pos hqa]
  have hden : R*(r.den : ℝ)*(qf : ℝ) = (qa : ℝ)*(R*(effectiveModulus a r qf : ℝ)) := by
    have hh : (r.den : ℝ)*(qf : ℝ) = (qa : ℝ)*(effectiveModulus a r qf : ℝ) := by
      exact_mod_cast denominator_full_cofactor a r qf hq
    linear_combination R*hh
  rw [hnum,hden]
  exact (mul_div_mul_left _ _ hqa.ne').symm

theorem effective_ratio_upper (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (R : ℝ)
    (hR : 0 < R) :
    |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) ≤
      1/R+|(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := by
  rw [effective_ratio_identity a r qf hq R]
  have hD : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hqR : (0 : ℝ) < qf := by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero
  have hb : (cofactorHit qf a : ℝ) ≤ qf := by exact_mod_cast (cofactorHit_spec qf hq a).2.1
  have hn : |(hitNumerator a r qf : ℝ)| ≤ (r.den : ℝ)*(qf : ℝ)+|(r.num : ℝ)| := by
    have hh := abs_sub ((r.den : ℝ)*(cofactorHit qf a : ℝ)) (r.num : ℝ)
    have hpos : 0 ≤ (r.den : ℝ)*(cofactorHit qf a : ℝ) := by positivity
    simp only [abs_of_nonneg hpos] at hh
    have hb' := mul_le_mul_of_nonneg_left hb hD.le
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
      hh.trans (add_le_add hb' le_rfl)
  calc
    _ ≤ ((r.den : ℝ)*(qf : ℝ)+|(r.num : ℝ)|)/(R*(r.den : ℝ)*(qf : ℝ)) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by field_simp

theorem effective_size_ratio_le (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hqf : Squarefree qf)
    (q : ℕ) (hq : 0 < q) (hqqf : q ≤ qf) (Sq R Z : ℝ)
    (_hSq : 0 ≤ Sq) (hR : 1 ≤ R) (hZ : 2 ≤ Z)
    (hSqratio : Sq/(q : ℝ) ≤ Z) (hA : |(r.num : ℝ)| ≤ Sq*R*Z^10) :
    effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ Z^12 := by
  have hRp : 0 < R := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hH : (0 : ℝ) < effectiveModulus a r qf := by exact_mod_cast effectiveModulus_pos a r qf
  have hD : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hqqfR : (q : ℝ) ≤ qf := by exact_mod_cast hqqf
  have hqD : (q : ℝ) ≤ (r.den : ℝ)*(qf : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    nlinarith
  have hnum : |(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) ≤ (Sq/(q : ℝ))*Z^10 := by
    calc
      _ ≤ |(r.num : ℝ)|/(R*(q : ℝ)) := div_le_div_of_nonneg_left (abs_nonneg _)
        (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hqD hRp.le])
      _ ≤ (Sq*R*Z^10)/(R*(q : ℝ)) := div_le_div_of_nonneg_right hA (by positivity)
      _ = _ := by field_simp
  have hpow : 1 ≤ Z^11 := one_le_pow₀ (by linarith)
  have hZ12 : 1+Z^11 ≤ Z^12 := by
    calc
      _ ≤ 2*Z^11 := by linarith
      _ ≤ Z*Z^11 := mul_le_mul_of_nonneg_right hZ (by positivity)
      _ = _ := by ring
  have hratio : |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) ≤ Z^12 := by
    calc
      _ ≤ 1/R+|(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := effective_ratio_upper a r qf hqf R hRp
      _ ≤ 1+(Sq/(q : ℝ))*Z^10 := add_le_add (div_le_self (by norm_num) hR) hnum
      _ ≤ 1+Z*Z^10 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hSqratio (show 0 ≤ Z^10 by positivity))
      _ = 1+Z^11 := by ring
      _ ≤ _ := hZ12
  apply (div_le_iff₀ hH).mpr
  apply max_le
  · have h1 : 1 ≤ Z^12 := by linarith [hZ12,pow_nonneg (by linarith : (0 : ℝ) ≤ Z) 11]
    nlinarith
  · have hh := (div_le_iff₀ hH).mp (show (|(effectiveIntercept a r qf : ℝ)|/R)/(effectiveModulus a r qf : ℝ) ≤ Z^12 by
        simpa only [div_div] using hratio)
    exact hh

end ErdosVarianceEffective



namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

theorem denominator_le_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    r.den ≤ effectiveModulus a r qf := by
  have hE := badPrimeProduct_pos (fun t => (a t : ℤ)) r qf
  dsimp [effectiveModulus]
  nlinarith

theorem nonaligned_le_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    badPrimeProduct (fun t => (a t : ℤ)) r qf ≤ effectiveModulus a r qf := by
  have hD := r.pos
  dsimp [effectiveModulus]
  nlinarith

theorem alignedCofactor_le_full (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor (fun t => (a t : ℤ)) r qf ≤ qf := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero)
  exact ⟨badPrimeProduct (fun t => (a t : ℤ)) r qf,(alignedCofactor_mul_bad _ r qf hq).symm⟩

theorem soft_effective_bounds (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R B : ℝ) (hR : 0 < R)
    (hsoft : effectiveSize a r qf R ≤ B) :
    (r.den : ℝ) ≤ B ∧ (badPrimeProduct (fun t => (a t : ℤ)) r qf : ℝ) ≤ B ∧
      |(effectiveIntercept a r qf : ℝ)| ≤ R*B := by
  have hH : (effectiveModulus a r qf : ℝ) ≤ B := (le_max_left _ _).trans hsoft
  have hC : |(effectiveIntercept a r qf : ℝ)|/R ≤ B := (le_max_right _ _).trans hsoft
  refine ⟨?_,?_,?_⟩
  · have hh : (r.den : ℝ) ≤ effectiveModulus a r qf := by exact_mod_cast denominator_le_effectiveModulus a r qf
    exact hh.trans hH
  · have hh : (badPrimeProduct (fun t => (a t : ℤ)) r qf : ℝ) ≤ effectiveModulus a r qf := by
      exact_mod_cast nonaligned_le_effectiveModulus a r qf
    exact hh.trans hH
  · have hh := (div_le_iff₀ hR).mp hC
    nlinarith

theorem large_factor_aligns_of_soft (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R B : ℝ) (hR : 0 < R)
    (hsoft : effectiveSize a r qf R ≤ B) (t : ℕ) (ht : t ∈ qf.primeFactors) (hlarge : B < (t : ℝ)) :
    aligns (fun u => (a u : ℤ)) r t := by
  classical
  by_contra hn
  have hmem : t ∈ badPrimeFactors (fun u => (a u : ℤ)) r qf := Finset.mem_filter.mpr ⟨ht,hn⟩
  have hd : t ∣ badPrimeProduct (fun u => (a u : ℤ)) r qf := Finset.dvd_prod_of_mem _ hmem
  have hle := Nat.le_of_dvd (badPrimeProduct_pos _ r qf) hd
  have hleR : (t : ℝ) ≤ badPrimeProduct (fun u => (a u : ℤ)) r qf := by exact_mod_cast hle
  have hbound := (soft_effective_bounds a r qf R B hR hsoft).2.1
  linarith

end ErdosVarianceEffective


namespace ErdosVarianceEffective
open ErdosInverseCells

theorem actual_numerator_triangle (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    |(r.num : ℝ)| ≤ (r.den : ℝ)*(qf : ℝ)+(qf : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
  have hEq : (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ) =
      (r.den : ℝ)*(cofactorHit qf a : ℝ)-(r.num : ℝ) := by
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ℝ)) (effectiveIntercept_identity a r qf hq)
  have hA : (r.num : ℝ) = (r.den : ℝ)*(cofactorHit qf a : ℝ)-
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ) := by linarith
  have hb : (cofactorHit qf a : ℝ) ≤ qf := by exact_mod_cast (cofactorHit_spec qf hq a).2.1
  have hqa : (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ) ≤ qf := by
    exact_mod_cast alignedCofactor_le_full a r qf hq
  rw [hA]
  calc
    _ ≤ |(r.den : ℝ)*(cofactorHit qf a : ℝ)|+
        |(alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ)| := abs_sub _ _
    _ = (r.den : ℝ)*(cofactorHit qf a : ℝ)+
        (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (r.den : ℝ)*(cofactorHit qf a : ℝ)),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_right hqa (abs_nonneg _))

theorem soft_global_heights (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : 0 < p) (R w Cs : ℝ) (hR : 0 < R) (hRp : R ≤ (p : ℝ))
    (hw : 2 ≤ w) (hY : p*qf ≤ Y) (hsoft : effectiveSize a r qf R ≤ w^Cs) :
    (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) := by
  have hb := soft_effective_bounds a r qf R (w^Cs) hR hsoft
  have hw0 : 0 < w := by linarith
  have hB : 0 ≤ w^Cs := Real.rpow_nonneg hw0.le _
  have hqY : (qf : ℝ) ≤ Y := by
    have hh : qf ≤ Y := (by nlinarith : qf ≤ p*qf).trans hY
    exact_mod_cast hh
  have hRqY : R*(qf : ℝ) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_right hRp (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hi : (p : ℝ)*(qf : ℝ) ≤ Y := by exact_mod_cast hY
    exact hh.trans hi
  refine ⟨hb.1,?_⟩
  have hA : |(r.num : ℝ)| ≤ 2*(Y : ℝ)*w^Cs := by
    have htri := actual_numerator_triangle a r qf hq
    have hDq := mul_le_mul_of_nonneg_right hb.1 (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hCq := mul_le_mul_of_nonneg_left hb.2.2 (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hqY' := mul_le_mul_of_nonneg_left hqY hB
    have hRqY' := mul_le_mul_of_nonneg_left hRqY hB
    nlinarith
  have hw2 : 2 ≤ w^2 := by nlinarith
  have hscale : 2*(Y : ℝ)*w^Cs ≤ (Y : ℝ)*w^(Cs+2) := by
    rw [Real.rpow_add hw0,Real.rpow_two]
    have hh := mul_le_mul_of_nonneg_left hw2 (mul_nonneg (Nat.cast_nonneg Y : (0 : ℝ) ≤ Y) hB)
    nlinarith
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hA.trans hscale

end ErdosVarianceEffective


section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceEffective
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseCells ErdosCofactorChoices ErdosPrimitiveIntercept
open NumberTheoryLean.LogarithmicBinScale

theorem source_effective_heights (Clen Cparent : ℝ) (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) :
    ∀ᶠ z : ℝ in atTop,∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i,m i : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
      ∀ (a : ℕ → ℕ) (r : ℚ) (q e p : ℕ) (R : ℝ),
      q ∈ cofactorChoices (actualBins z xi) m → 0 < e → 0 < p → Squarefree (q*e) → 1 ≤ R →
      p*(q*e) ≤ sourceY z →
      Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent →
      ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ) ≤ R*(sourceZ z)^10 →
      (r.num.natAbs : ℝ) ≤ cofactorScale z xi m*R*(sourceZ z)^10 →
      (effectiveModulus a r (q*e) : ℝ) ≤ R*(sourceZ z)^11 ∧
        effectiveSize a r (q*e) R/(effectiveModulus a r (q*e) : ℝ) ≤ (sourceZ z)^12 := by
  filter_upwards [source_span_geometry,source_extension_le_Z Cparent hCparent,
    source_bin_factor_subpower Clen 1 hClen zero_lt_one,sourceZ_tendsto_atTop.eventually_ge_atTop 2]
    with z hspan hext hfactor hZ
  intro xi hxi hxi1 m hm a r q e p R hq he hp hqf hR hFinal hParent hStructure hRaw
  have hqpos := actual_cofactor_positive hspan.1 hspan.2.1 hxi m q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have heZ := hext p q e hp hqpos he hFinal hParent
  refine ⟨effectiveModulus_height_of_extension a r q e hqpos he R (sourceZ z) (by linarith)
    (by linarith) hStructure heZ,?_⟩
  have hrange := actual_cofactor_range hspan.1 hspan.2.1 hxi m q hq
  have hratio : cofactorScale z xi m/(q : ℝ) ≤ sourceZ z := by
    calc
      _ ≤ (1+xi)^(∑ i,m i) := by
        apply (div_le_iff₀ hqR).mpr
        have hh := (div_le_iff₀ (pow_pos (by linarith : 0 < 1+xi) _)).mp hrange.1
        nlinarith
      _ ≤ _ := by simpa only [Real.rpow_one] using hfactor xi (∑ i,m i) hxi hxi1 hm
  have hqle : q ≤ q*e := by nlinarith
  have hA : |(r.num : ℝ)| ≤ cofactorScale z xi m*R*(sourceZ z)^10 := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hRaw
  exact effective_size_ratio_le a r (q*e) hqf q hqpos hqle (cofactorScale z xi m) R (sourceZ z)
    (actual_cofactorScale_pos hspan.1 hspan.2.1 hxi m).le hR hZ hratio hA

end ErdosVarianceEffective

end


namespace ErdosVarianceEffective
open ErdosInverseAlignment

theorem soft_full_factor_alignment (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (halign : aligns (fun t => (a t : ℤ)) r p)
    (R B : ℝ) (hR : 0 < R) (hsoft : effectiveSize a r qf R ≤ B) :
    ∀ t ∈ (p*qf).primeFactors,B < (t : ℝ) → aligns (fun u => (a u : ℤ)) r t := by
  intro t ht hlarge
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors] at ht
  rcases Finset.mem_union.mp ht with ht | ht
  · have he : t = p := Finset.mem_singleton.mp ht
    exact he.symm ▸ halign
  · exact large_factor_aligns_of_soft a r qf R B hR hsoft t ht hlarge

theorem soft_endpoint_eligible (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (halign : aligns (fun t => (a t : ℤ)) r p)
    (R w Cs : ℝ) (hR : 0 < R) (hRp : R ≤ (p : ℝ)) (hw : 2 ≤ w)
    (hY : p*qf ≤ Y) (hsoft : effectiveSize a r qf R ≤ w^Cs) :
    (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) ∧
      ∀ t ∈ (p*qf).primeFactors,Cs < Real.logb w (t : ℝ) → aligns (fun u => (a u : ℤ)) r t := by
  have hheight := soft_global_heights Y a r qf hq p hp.pos R w Cs hR hRp hw hY hsoft
  refine ⟨hheight.1,hheight.2,?_⟩
  intro t ht hlog
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_mem_primeFactors ht
  have hpow : w^Cs < (t : ℝ) := (Real.lt_logb_iff_rpow_lt (by linarith : 1 < w) htpos).mp hlog
  exact soft_full_factor_alignment a r qf hq p hp halign R (w^Cs) hR hsoft t ht hpow

end ErdosVarianceEffective


section

open _root_.Filter
namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry BoundedEdgeBins CofactorAllChoiceBounds ParentCofactorChoices ParentTailPartition BinCutSelections
  StructuredWitnessOutside EndpointCofactorSplit FullIsolatedCofactor SingletonBinSelection TwoPrimeObservableSum
  ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEffective ErdosInverseBoxHeight
  ErdosInverseCells ErdosInverseAlignment ErdosPrimitiveIntercept
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem structured_endpoint_heights (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∀ᶠ top : ℝ in atTop,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 2*C*xi ≤ 1 →
      ∀ (hw : 1 < sourceW top) (htop : sourceW top < top) (K aStar X : ℝ),0 ≤ aStar →
      ∀ (z : Node),0 < sourceY top →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
        Valid z.side z.ratio → Consistent z → StrongState z → z.closed = true → (sourceW top)^z.cutoff = top →
      ∀ (m : Fin (binCount (sourceW top) top xi) → ℕ),SafeAnchor hw htop hxi C (sourceB top) K z m →
      ∀ f ∈ selections (globalBins (sourceW top) top xi) m,
      ∀ (i j : Fin (binCount (sourceW top) top xi)),j < i → m i = 1 →
        boundedEdgeBin (sourceW top) top xi (sourceY top) m M X j →
      ∀ (residue : ℕ → ℕ) (r : ℚ) (cp : ℝ),
        r ∈ sourceRationalList (globalBins (sourceW top) top xi i) (fun t => (residue t : ℤ))
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp →
        ((r.den*badPrimeProduct (fun t => (residue t : ℤ)) r (selectionProduct (parentCofactorSelection f i j)) : ℕ) : ℝ) ≤
          lower (sourceW top) top xi i*(sourceZ top)^10 →
        (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤
          lower (sourceW top) top xi i*(sourceZ top)^11 ∧
        effectiveSize residue r (selectionProduct (eraseSelection f i)) (lower (sourceW top) top xi i)/
          (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ (sourceZ top)^12 := by
  filter_upwards [source_effective_heights C (M+1) hC (by linarith),
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually] with top hheights hscale
  intro xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap m hanchor
    f hf i j hji hi hj residue r cp hraw hstructure
  let P := globalBins (sourceW top) top xi
  let cm := parentCofactorMultiplicity m i j
  let p := pickedPrime f i
  let q := selectionProduct (parentCofactorSelection f i j)
  let e := pickedPrime f j*selectionProduct (belowSelection f j)
  let qf := selectionProduct (eraseSelection f i)
  let R := lower (sourceW top) top xi i
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hmj := bounded_edge_singleton m j hj
  have hcoords := full_selection_coordinates P m f hf i j hi hmj
  have hp : p ∈ P i := hcoords.1
  have hq : q ∈ cofactorChoices (actualBins top xi) cm := hcoords.2.2
  have hppos : 0 < p := (bin_prime_in_source (zero_lt_one.trans hw) htop hxi i hp).1.pos
  have he : 0 < e := endpoint_extra_factor_pos hw htop hxi m f hf j hmj
  have hsplit : qf = q*e := endpoint_cofactor_split hw htop hxi m f hf i j hji hmj
  have hfErase := erase_selection_mem P m f hf i
  have hQf := (erased_cofactor_arithmetic hw htop hxi m i (eraseSelection f i) hfErase).1
  have hQsplit : Squarefree (q*e) := hsplit ▸ hQf
  have hprod : selectionProduct f = p*qf := isolated_product P m f hf i hi
  have hprodPos : 0 < selectionProduct f := by
    rw [hprod]
    exact Nat.mul_pos hppos (Nat.pos_of_ne_zero hQf.ne_zero)
  have htotal := full_box_total_length_lower hw htop hxi hC hcomp (sourceY top) hY z hroot
    hs hz hg hclosed hcap m hanchor f hf
  have hFinal := product_le_Y_of_length (sourceW top) aStar hw ha (sourceY top) (selectionProduct f) hY hprodPos htotal
  rw [hprod,hsplit] at hFinal
  have hRlow : sourceW top ≤ R := (bin_source_bounds (zero_lt_one.trans hw) htop hxi i).1
  have hR1 : 1 ≤ R := hw.le.trans hRlow
  have hparent := (cofactor_all_choice_lengths hw htop hxi hC hcomp (sourceY top) hY z hroot
    hs hz hg hclosed hcap m hanchor i j hji hi hj).1 q hq p hp
  have hparentBound : Real.logb (sourceW top) ((sourceY top : ℝ)/((p : ℝ)*q)) ≤ M+1 :=
    hparent.trans (by linarith)
  have hlen := anchor_total_length hw htop hxi z m hanchor
  have hcm : ((∑ k,cm k : ℕ) : ℝ) ≤ C*Real.log (sourceB top) :=
    (Nat.cast_le.mpr (cofactor_total_le m i j)).trans hlen
  have hSq := actual_cofactorScale_pos (zero_lt_one.trans hw) htop hxi cm
  have hnum := ((mem_sourceRationalList (P i) (fun t => (residue t : ℤ)) hSq.le
    (show 0 ≤ R by linarith) r).mp hraw).1
  have hh := hheights xi hxi hxi1 cm hcm residue r q e p R hq he hppos hQsplit hR1 hFinal
    hparentBound hstructure hnum
  simpa only [← hsplit] using hh

end ErdosVarianceEligible

end


namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
  FullIsolatedCofactor ErdosVarianceWeighted
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem full_endpoint_data {w top xi B C K aStar : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C) (ha : 0 ≤ aStar)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-aStar+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (i : Fin (binCount w top xi)) (hi : m i = 1) :
    Squarefree (selectionProduct (eraseSelection f i)) ∧ (pickedPrime f i).Prime ∧
      pickedPrime f i ∈ globalBins w top xi i ∧
      pickedPrime f i*selectionProduct (eraseSelection f i) ≤ Y := by
  obtain ⟨p,hp,hfi,_hfill⟩ := singleton_selection_recovery _ m i hi f hf
  have hpmem : pickedPrime f i ∈ globalBins w top xi i := by simpa [pickedPrime,hfi] using hp
  have hprime := (bin_prime_in_source (zero_lt_one.trans hw) htop hxi i hpmem).1
  have hsq := (erased_cofactor_arithmetic hw htop hxi m i (eraseSelection f i)
    (erase_selection_mem _ m f hf i)).1
  have hlen := full_box_total_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m hanchor f hf
  rw [isolated_product _ m f hf i hi] at hlen
  refine ⟨hsq,hprime,hpmem,?_⟩
  exact product_le_Y_of_length w aStar hw ha Y _ hY
    (Nat.mul_pos hprime.pos (Nat.pos_of_ne_zero hsq.ne_zero)) hlen

end ErdosVarianceEligible


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_GuardedHardPrimeSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseCounts ErdosInverseAlignment ErdosVarianceCommon
attribute [local instance] Classical.propDecidable

theorem mem_badAligningPrimes (P : Finset ℕ) (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (r : ℚ) (qf : ℕ) (eps : ℝ) (p : ℕ) :
    p ∈ badAligningPrimes P Y w a r qf eps ↔ p ∈ P ∧
      aligns (fun t => (a t : ℤ)) r p ∧
      eps < |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*qf) : ℝ)/
        referenceCount Y w p qf-1| := Finset.mem_filter

end ErdosVarianceSmallPrime



namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem mem_rawHardPrimeUnion (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) (p : ℕ) :
    p ∈ rawHardPrimeUnion Q z R theta a qf Cs eps ↔ ∃ r ∈ Q,
      hardCandidate z R a r qf Cs ∧
      p ∈ badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps := by
  simp only [rawHardPrimeUnion,Finset.mem_biUnion]
  apply exists_congr
  intro r
  apply and_congr_right
  intro _hr
  by_cases h : hardCandidate z R a r qf Cs <;> simp [guardedHardPrimes,h]

end ErdosVarianceWeighted


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricSelectionHardMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport SafeSubsetBoxGeometry
  GeometricBoxImages ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection CanonicalSubsetBox
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition LogarithmicBinMaps
  ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem geometric_selection_hard_mass (C aStar alpha eps tau Cmin : ℝ) (F : ℕ)
    (hC : 1 ≤ C) (ha : 0 < aStar) (halpha : 0 < alpha) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi0 → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ (K L : ℝ) (z : Node),z.side = .even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff = sourceB top → z.closed = true →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (sourceB top) K L alpha (1/100) z,
      ∀ i : Fin (binCount (sourceW top) top xi),m i = 1 → top^alpha ≤ lower (sourceW top) top xi i →
      ∀ (a : ℕ → ℕ) (Q : Finset ℚ),Q.card ≤ F →
        (∑ f ∈ (selections (globalBins (sourceW top) top xi) m).filter
          (hardSelection Q top (lower (sourceW top) top xi i) (width (sourceW top) top xi i) a i Cs eps),
          (selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_selection_hard_mass_jb247 alpha aStar eps tau Cmin F halpha ha heps htau
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  have hBT := JacobsthalSourceScale.sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hsource xi hxi hxib,source_span_geometry,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually,
    source_B_bounds,hBT.eventually_ge_atTop 3] with top hv hspan hscale hBounds hB3
  have hw : 1 < sourceW top := hscale.1
  have htop : sourceW top < top := hspan.2.1
  have htop0 : 0 < top := (zero_lt_one.trans hw).trans htop
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hlog : 1 ≤ Real.log (sourceW top) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hBounds.1
  have hsmall : 2*(xi/Real.log (sourceW top)) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hspanMul : (1+xi)*sourceW top ≤ top := by
    have hh := hspan.2.2 xi hxi hxi1
    have hd : 0 < top/sourceW top := div_pos htop0 (zero_lt_one.trans hw)
    have he := (Real.log_le_log_iff (by positivity : 0 < 1+xi) hd).mp hh
    exact (le_div_iff₀ (zero_lt_one.trans hw)).mp he
  have hwidth := common_width_bounds (zero_lt_one.trans hw) htop hxi hxi1 hspanMul
  refine ⟨hw,htop,?_⟩
  intro K L z heven h199 hz hcut hclosed hroot m hm i hi hiR a Q hQ
  have hs : Valid z.side z.ratio := by rw [heven];change 198/100 ≤ z.ratio;linarith
  have hStrong := source_strong_state hB3 z heven h199 hz hcut
  have hY : 0 < sourceY top := by
    by_contra! hzero
    have he : sourceY top = 0 := by omega
    rw [he,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    linarith [hStrong.1]
  have hcap : (sourceW top)^z.cutoff = top := by
    rw [hcut]
    exact (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log htop0)
  have hanchor := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hgeometry := full_box_variance_fibres hw htop hxi (by linarith : 0 ≤ C) ha.le hcomp
    (sourceY top) hY z hroot hs hz hStrong hclosed hcap m hanchor i hi
  have hthetal : xi/4 ≤ width (sourceW top) top xi i := by rw [hwidth.2.2.2 i];exact hwidth.2.1
  have hthetau : width (sourceW top) top xi i ≤ xi := by rw [hwidth.2.2.2 i];exact hwidth.2.2.1
  exact hv (lower (sourceW top) top xi i) (width (sourceW top) top xi i) hiR hthetal hthetau a _
    (globalBins (sourceW top) top xi) m i hi rfl hgeometry Q hQ

end ErdosVarianceWeighted


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EndpointSoftConclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEligible
open NumberTheoryLean ErdosVarianceWeighted ErdosVarianceEffective ErdosVarianceSmallPrime ErdosInverseBoxHeight
attribute [local instance] Classical.propDecidable

theorem soft_of_not_guarded_hard (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (Cs eps : ℝ) (hr : r ∈ Q)
    (hH : (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11)
    (hRatio : effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12)
    (hbad : p ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY z) (sourceW z) a r qf eps)
    (hout : p ∉ rawHardPrimeUnion Q z R theta a qf Cs eps) :
    effectiveSize a r qf R < (sourceW z)^Cs := by
  by_contra! hhard
  apply hout
  exact (mem_rawHardPrimeUnion Q z R theta a qf Cs eps p).mpr ⟨r,hr,⟨hH,hRatio,hhard⟩,hbad⟩

theorem soft_guarded_point_eligible (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (Cs eps : ℝ) (hr : r ∈ Q) (hq : Squarefree qf) (hp : p.Prime) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hw : 2 ≤ sourceW z) (hY : p*qf ≤ sourceY z)
    (hH : (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11)
    (hRatio : effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12)
    (hbad : p ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY z) (sourceW z) a r qf eps)
    (hout : p ∉ rawHardPrimeUnion Q z R theta a qf Cs eps) :
    (r.den : ℝ) ≤ (sourceW z)^Cs ∧ (r.num.natAbs : ℝ) ≤ (sourceY z : ℝ)*(sourceW z)^(Cs+2) ∧
      ∀ t ∈ (p*qf).primeFactors,Cs < Real.logb (sourceW z) (t : ℝ) →
        ErdosInverseAlignment.aligns (fun u => (a u : ℤ)) r t := by
  have hsoft := soft_of_not_guarded_hard Q z R theta a r qf p Cs eps hr hH hRatio hbad hout
  have halign := ((mem_badAligningPrimes _ _ _ _ _ _ _ _).mp hbad).2.1
  exact soft_endpoint_eligible (sourceY z) a r qf hq p hp halign R (sourceW z) Cs hR hRp hw hY hsoft.le

end ErdosVarianceEligible

end

section

namespace ErdosVarianceEligible
open NumberTheoryLean ErdosVarianceWeighted ErdosVarianceEffective ErdosVarianceSmallPrime ErdosInverseBoxHeight
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
attribute [local instance] Classical.propDecidable

theorem endpoint_soft_conclusion {n : ℕ} (Q : Finset ℚ) (top R theta : ℝ) (residue : ℕ → ℕ)
    (f : Fin n → Finset ℕ) (i : Fin n) (r : ℚ) (Cs eps : ℝ)
    (hr : r ∈ Q) (hSq : Squarefree (selectionProduct (eraseSelection f i)))
    (hp : (pickedPrime f i).Prime) (hR : 0 < R) (hRp : R ≤ (pickedPrime f i : ℝ))
    (hw : 2 ≤ sourceW top) (hY : pickedPrime f i*selectionProduct (eraseSelection f i) ≤ sourceY top)
    (hH : (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ R*(sourceZ top)^11)
    (hRatio : effectiveSize residue r (selectionProduct (eraseSelection f i)) R/
      (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ (sourceZ top)^12)
    (hbad : pickedPrime f i ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY top) (sourceW top)
      residue r (selectionProduct (eraseSelection f i)) eps)
    (hout : ¬hardSelection Q top R theta residue i Cs eps f) :
    (r.den : ℝ) ≤ (sourceW top)^Cs ∧ (r.num.natAbs : ℝ) ≤ (sourceY top : ℝ)*(sourceW top)^(Cs+2) ∧
      ∀ t ∈ (pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
        Cs < Real.logb (sourceW top) (t : ℝ) → ErdosInverseAlignment.aligns (fun u => (residue u : ℤ)) r t :=
  soft_guarded_point_eligible Q top R theta residue r (selectionProduct (eraseSelection f i)) (pickedPrime f i)
    Cs eps hr hSq hp hR hRp hw hY hH hRatio hbad hout

end ErdosVarianceEligible

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_WeightedTwoExceptions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEligible
attribute [local instance] Classical.propDecidable

theorem weighted_two_exceptions {α : Type*} (S : Finset α) (weight : α → ℝ)
    (E A B : α → Prop) (hw : ∀ x ∈ S,0 ≤ weight x)
    (hsub : ∀ x ∈ S,E x → A x ∨ B x) :
    (∑ x ∈ S.filter E,weight x) ≤ (∑ x ∈ S.filter A,weight x)+(∑ x ∈ S.filter B,weight x) := by
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : E x
  · rcases hsub x hx he with ha|hb
    · simp only [ite_eq_left he,ite_eq_left ha]
      split_ifs <;> linarith [hw x hx]
    · simp only [ite_eq_left he,ite_eq_left hb]
      split_ifs <;> linarith [hw x hx]
  · simp only [ite_eq_right he]
    split_ifs <;> linarith [hw x hx]

end ErdosVarianceEligible

end

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



namespace ErdosVarianceEligible
open NumberTheoryLean ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
  FullIsolatedCofactor ActualBinOwners SourceStopPredicate ActualCountErrorEdges
  ErdosVarianceSmallPrime ErdosVarianceCommon ErdosInverseAlignment
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

theorem eligible_word_witness_of_endpoint {w top xi Cs : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i = 1)
    (residue : ℕ → ℕ) (Q : Finset ℚ) (r : ℚ) (hr : r ∈ Q)
    (hsoft : (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) ∧
      ∀ t ∈ (pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
        Cs < Real.logb w (t : ℝ) → aligns (fun u => (residue u : ℤ)) r t) :
    eligibleWordWitness Y w Cs residue Q (descendingWord f) := by
  refine ⟨r,hr,⟨hsoft.1,hsoft.2.1⟩,?_⟩
  apply full_cofactor_alignment_word hw htop hxi m f hf i hi (sourceClass residue) r
  intro p hp hhigh
  exact hsoft.2.2 p hp hhigh

theorem word_error_bad_aligning_prime {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i : Fin (binCount w top xi)) (hi : m i = 1)
    (residue : ℕ → ℕ) (r : ℚ) (eps : ℝ) (halign : aligns (sourceClass residue) r (pickedPrime f i))
    (hbad : eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)|) :
    pickedPrime f i ∈ badAligningPrimes (globalBins w top xi i) Y w residue r
      (selectionProduct (eraseSelection f i)) eps := by
  obtain ⟨p,hp,hfi,_hfill⟩ := singleton_selection_recovery _ m i hi f hf
  have hpmem : pickedPrime f i ∈ globalBins w top xi i := by simpa [pickedPrime,hfi] using hp
  have hprod := full_word_isolated_product hw htop hxi m f hf i hi
  apply (mem_badAligningPrimes _ _ _ _ _ _ _ _).mpr
  refine ⟨hpmem,halign,?_⟩
  simpa only [wordCountError,relativeCountError,hprod,Nat.cast_mul,referenceCount] using hbad

end ErdosVarianceEligible



open _root_.Filter
namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry BoundedEdgeBins ParentCofactorChoices ParentTailPartition
  RawBoxRationalWitness SingletonBinSelection TwoPrimeObservableSum ActualCountErrorEdges
  ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEffective ErdosInverseBoxHeight
  ErdosInverseCells ErdosInverseAlignment ErdosInverseBoxApplication ErdosInverseSampleCost ErdosInverseCounts
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem outside_exceptions_eligible_word (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∀ᶠ top : ℝ in atTop,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 2*C*xi ≤ 1 →
      ∀ (hw : 1 < sourceW top) (htop : sourceW top < top) (K aStar X : ℝ),0 ≤ aStar →
      ∀ z : Node,0 < sourceY top →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
        Valid z.side z.ratio → Consistent z → StrongState z → z.closed = true → (sourceW top)^z.cutoff = top →
      ∀ m : Fin (binCount (sourceW top) top xi) → ℕ,SafeAnchor hw htop hxi C (sourceB top) K z m →
      ∀ f ∈ selections (globalBins (sourceW top) top xi) m,
      ∀ i : Fin (binCount (sourceW top) top xi),m i = 1 →
      ∀ J : Finset (Fin (binCount (sourceW top) top xi)),
        (∀ j ∈ J,boundedEdgeBin (sourceW top) top xi (sourceY top) m M X j ∧ j < i) →
      ∀ (residue : ℕ → ℕ) (delta cp sigma Cs eps : ℝ) (F : ℕ),
        (∀ j ∈ J,SourceInverseConclusion (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊)
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp sigma F
          (globalBins (sourceW top) top xi i)
          (cofactorChoices (globalBins (sourceW top) top xi) (parentCofactorMultiplicity m i j)) (globalBins (sourceW top) top xi j)) →
        (∃ j ∈ J,WitnessingBadEdge (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (pickedPrime f i)
          (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) →
        eps < |wordCountError (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (descendingWord f)| →
        (¬∃ j ∈ J,actualWitness (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
          (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (globalBins (sourceW top) top xi i)
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp
          (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)) →
        let Q := rawBoxList (globalBins (sourceW top) top xi) i J residue
          (fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp
        ¬hardSelection Q top (lower (sourceW top) top xi i) (width (sourceW top) top xi i) residue i Cs eps f →
        eligibleWordWitness (sourceY top) (sourceW top) Cs residue Q (descendingWord f) := by
  filter_upwards [structured_endpoint_heights C M hC hM,
    ErdosInverseEuler.sourceW_tendsto_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually]
    with top hheight hw2 hscale
  intro xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap m hanchor
    f hf i hi J hJ residue delta cp sigma Cs eps F hInv hbadEdge hbadWord hnoInv
  dsimp only
  intro hnoHard
  let P := globalBins (sourceW top) top xi
  let S := fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)
  let R := lower (sourceW top) top xi i
  let Q := rawBoxList P i J residue S R (sourceZ top) cp
  have hj : ∀ j ∈ J,m j = 1 := fun j hj => bounded_edge_singleton m j (hJ j hj).1
  obtain ⟨j,hjJ,r,hrQ,hrLocal,halign,hstructure⟩ := raw_box_witness P m i J f hf hi hj
    (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
    (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) S R (sourceZ top) cp sigma F hInv hbadEdge hnoInv
  have hbounds := hheight xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap
    m hanchor f hf i j (hJ j hjJ).2 hi (hJ j hjJ).1 residue r cp hrLocal hstructure
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hdata := full_endpoint_data hw htop hxi hC ha hcomp (sourceY top) hY z hroot hs hz hg hclosed hcap
    m hanchor f hf i hi
  have hR : 0 < R := (zero_lt_one.trans hw).trans_le (bin_source_bounds (zero_lt_one.trans hw) htop hxi i).1
  have hwidth : 0 ≤ width (sourceW top) top xi i := (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hRp := ((ErdosInversePrimeBin.mem_primeBin hR.le hwidth (pickedPrime f i)).mp hdata.2.2.1).2.1.le
  have hbad := word_error_bad_aligning_prime hw htop hxi (sourceY top) m f hf i hi residue r eps halign hbadWord
  have hsoft := endpoint_soft_conclusion Q top R (width (sourceW top) top xi i) residue f i r Cs eps
    hrQ hdata.1 hdata.2.1 hR hRp hw2 hdata.2.2.2 hbounds.1 hbounds.2 hbad hnoHard
  exact eligible_word_witness_of_endpoint hw htop hxi (sourceY top) m f hf i hi residue Q r hrQ hsoft

end ErdosVarianceEligible


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



open _root_.Filter
namespace ErdosVarianceFactory
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry GeometricBoxImages GeometricCandidateCount GeometricRangeCandidateUnion
  GeometricRegularWords BoundedEdgeBins BoundedCandidateCount CandidateExceptionMass
  ParentCofactorChoices ParentTailPartition SingletonBinSelection TwoPrimeObservableSum CanonicalSubsetBox
  RawBoxRationalWitness ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEligible
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseCells ErdosInverseCounts ErdosInverseAlignment
  ErdosInverseBoxApplication ErdosInverseSampleCost
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_raw_box_factory_jb247_oai (C K aStar alpha eps tau Cmin : ℝ)
    (hC : 1 ≤ C) (hK : 3 ≤ K) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Kstar : ℝ,K+10 < Kstar ∧ ∃ NQ : ℕ,∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ 2*Kstar+4 ≤ Cs ∧
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi0 → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ z : Node,z.side = .even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff = sourceB top → z.closed = true →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
      ∀ residue : ℕ → ℕ,
      ∀ m ∈ geometricBoxes hw htop hxi C (sourceB top) K (2*Kstar+5) alpha (1/100) z,
      ∃ Q : Finset ℚ,Q.card ≤ NQ ∧
        (∑ f ∈ (selections (globalBins (sourceW top) top xi) m).filter
          (unwitnessedSelection hw htop hxi (sourceY top) Cs C (sourceB top) K (2*Kstar+5) alpha (1/100) eps residue z Q),
          (selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m := by
  obtain ⟨Kstar,B0,w0,hKs,hB0,_hw0,hrecent⟩ := geometric_selection_recent_witness_jb247 K eps hK heps
  have hKs0 : 0 ≤ Kstar := by linarith
  let M := 2*Kstar+3
  have hM : 0 ≤ M := by dsimp [M] <;> linarith
  have hH : 0 < ⌈2*Kstar+10⌉₊ := by
    have hh := Nat.le_ceil (2*Kstar+10)
    by_contra! hn
    have he : ⌈2*Kstar+10⌉₊ = 0 := by omega
    rw [he,Nat.cast_zero] at hh
    linarith
  let delta := eps/(4*(⌈2*Kstar+10⌉₊ : ℝ))
  have hdelta : 0 < delta := by dsimp [delta] <;> positivity
  let sigma := min 1 (tau/(2*((⌈M⌉₊ : ℝ)+1)))
  have hsigma : 0 < sigma := lt_min zero_lt_one (by positivity)
  have hsigma1 : sigma ≤ 1 := min_le_left _ _
  have hsigmaBudget : (⌈M⌉₊ : ℝ)*sigma ≤ tau/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*((⌈M⌉₊ : ℝ)+1) by positivity)).mp
      (min_le_right (1 : ℝ) (tau/(2*((⌈M⌉₊ : ℝ)+1))))
    change sigma*(2*((⌈M⌉₊ : ℝ)+1)) ≤ tau at hh
    nlinarith
  obtain ⟨cp,_hcp,F,xiI,hxiI,hxiI1,hInverse⟩ := geometric_range_candidate_union_jb247 C Kstar aStar alpha delta sigma
    hC hKs0 ha ha1 halpha hdelta hsigma hsigma1
  let NQ := ⌈M⌉₊*F
  let requiredCs := max Cmin (2*Kstar+4)
  obtain ⟨Cs,hCs,hCsReq,xiH,hxiH,_hxiH1,hHard⟩ :=
    geometric_selection_hard_mass C aStar alpha eps (tau/2) requiredCs NQ hC ha halpha heps (by positivity)
  have hCsMin : Cmin ≤ Cs := (le_max_left _ _).trans hCsReq
  have hCsK : 2*Kstar+4 ≤ Cs := (le_max_right _ _).trans hCsReq
  have hCpos : 0 < C := by linarith
  let xi0 := min xiI (min xiH (1/(2*C)))
  have hxi0 : 0 < xi0 := lt_min hxiI (lt_min hxiH (by positivity))
  have hxi01 : xi0 ≤ 1 := (min_le_left _ _).trans hxiI1
  refine ⟨Kstar,hKs,NQ,Cs,hCs,hCsMin,hCsK,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxiInv : xi ≤ xiI := hxib.trans (min_le_left _ _)
  have hxiHard : xi ≤ xiH := (hxib.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hxiDelta : xi ≤ 1/(2*C) := (hxib.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hDelta : 2*C*xi ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp hxiDelta
    nlinarith
  have hxi1 := hxib.trans hxi01
  have hBT := JacobsthalSourceScale.sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hInverse xi hxi hxiInv,hHard xi hxi hxiHard,
    outside_exceptions_eligible_word C M (by linarith : 0 ≤ C) hM,
    hBT.eventually_ge_atTop B0,sourceW_tendsto_atTop.eventually_ge_atTop w0,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually,source_B_bounds]
    with top hInvTop hHardTop hOutside hB hwMin hscale hWbounds
  obtain ⟨hw,htop,hInvData⟩ := hInvTop
  obtain ⟨_hwH,_htopH,hHardData⟩ := hHardTop
  have hB3 : 3 ≤ sourceB top := hB0.trans hB
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hlog : 1 ≤ Real.log (sourceW top) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hWbounds.1
  have hsmall : 2*(xi/Real.log (sourceW top)) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hpower : (sourceW top)^(sourceB top) = top :=
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log ((zero_lt_one.trans hw).trans htop))
  refine ⟨hw,htop,?_⟩
  intro z heven h199 hz hcut hclosed hroot residue m hm
  have hs : Valid z.side z.ratio := by rw [heven];change 198/100 ≤ z.ratio;linarith
  have hStrong := source_strong_state hB3 z heven h199 hz hcut
  have hY : 0 < sourceY top := by
    by_contra! hn
    have hzero : sourceY top = 0 := by omega
    rw [hzero,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    linarith [hStrong.1]
  have hcap : (sourceW top)^z.cutoff = top := by rwa [hcut]
  have hanchor := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  obtain ⟨i,hmi,hRi,_hRiUpper,hStep,hInvMass⟩ :=
    hInvData K (2*Kstar+5) z heven h199 hz hcut hclosed hroot m hm
  let P := globalBins (sourceW top) top xi
  let J := candidateBins (sourceW top) top xi (sourceY top) m M M
  let S := fun j => cofactorScale top xi (parentCofactorMultiplicity m i j)
  let R := lower (sourceW top) top xi i
  let Q := rawBoxList P i J residue S R (sourceZ top) cp
  have hJ : ∀ j ∈ J,boundedEdgeBin (sourceW top) top xi (sourceY top) m M M j ∧ j < i := by
    intro j hj
    have hb := (Finset.mem_filter.mp hj).2
    exact ⟨hb,(hStep j hb residue).1⟩
  have hInv : ∀ j ∈ J,SourceInverseConclusion (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
      residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (S j) R (sourceZ top) cp sigma F
      (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) :=
    fun j hj => (hStep j (hJ j hj).1 residue).2.2.1
  have hJcard : J.card ≤ ⌈M⌉₊ := geometric_candidate_card hw htop hxi hC hlog hcomp hB3 ha.le
    (sourceY top) hY z hroot heven h199 hz hcut hclosed hpower m hm
  have hQcard : Q.card ≤ NQ :=
    (raw_box_list_card P m i J (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊)
      residue delta (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) S R (sourceZ top) cp sigma F hInv).trans
      (Nat.mul_le_mul_right F hJcard)
  refine ⟨Q,hQcard,?_⟩
  let EInv := fun f => ∃ j ∈ J,actualWitness (sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊sourceW top⌋₊) residue delta
    (SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (P i) (S j) R (sourceZ top) cp
      (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)
  let EHard := hardSelection Q top R (width (sourceW top) top xi i) residue i Cs eps
  let E := unwitnessedSelection hw htop hxi (sourceY top) Cs C (sourceB top) K (2*Kstar+5) alpha (1/100) eps residue z Q
  have hsub : ∀ f ∈ selections P m,E f → EInv f ∨ EHard f := by
    intro f hf hE
    by_cases hEI : EInv f
    · exact Or.inl hEI
    by_cases hEH : EHard f
    · exact Or.inr hEH
    have hgeom := hE.1
    have hbad := hE.2.1
    obtain ⟨j,hjb,hEdge⟩ := hrecent (sourceB top) (sourceW top) top hB hwMin hw htop xi hxi C hC hcomp
      aStar alpha (1/100) ha.le ha1 (sourceY top) hY z hroot heven h199 hz hcut hclosed hpower
      residue m f hf hgeom hbad
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjb⟩
    have hWitness := hEdge i hmi (hJ j hjJ).2
    have hEligible := hOutside xi hxi hxi1 hDelta hw htop K aStar M ha.le z hY hroot hs hz hStrong hclosed hcap
      m hanchor f hf i hmi J hJ residue delta cp sigma Cs eps F hInv ⟨j,hjJ,hWitness⟩ hbad hEI hEH
    exact False.elim (hE.2.2 hEligible)
  have hInvBound : (∑ f ∈ (selections P m).filter EInv,(selectionProduct f : ℝ)⁻¹) ≤
      (⌈M⌉₊ : ℝ)*sigma*selectionMass P m := hInvMass residue
  have hHardBound : (∑ f ∈ (selections P m).filter EHard,(selectionProduct f : ℝ)⁻¹) ≤
      (tau/2)*selectionMass P m :=
    hHardData K (2*Kstar+5) z heven h199 hz hcut hclosed hroot m hm i hmi hRi residue Q hQcard
  have hmass0 : 0 ≤ selectionMass P m := Finset.sum_nonneg (fun _ _ => by positivity)
  have hbudget := mul_le_mul_of_nonneg_right hsigmaBudget hmass0
  have hbound := weighted_two_exceptions (selections P m) (fun f => (selectionProduct f : ℝ)⁻¹) E EInv EHard
    (fun _ _ => by positivity) hsub
  change (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass P m
  have hfI := Finset.filter_congr_decidable (selections P m) EInv (fun f => Classical.propDecidable (EInv f))
  simp only [hfI] at hbound
  have hsummed := hbound.trans (add_le_add hInvBound hHardBound)
  apply hsummed.trans
  calc
    _ ≤ (tau/2)*selectionMass P m+(tau/2)*selectionMass P m := add_le_add hbudget le_rfl
    _ = _ := by ring

end ErdosVarianceFactory


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247_oai := @OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247_oai
