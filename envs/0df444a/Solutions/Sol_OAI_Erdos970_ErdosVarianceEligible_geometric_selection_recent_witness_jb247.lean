-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceEligible.geometric_selection_recent_witness_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:36.162802+00:00
-- url     : https://prove2.me/submissions/185069f1-667b-4ec2-9441-ba04cecbe159

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

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositiveProgression
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem lt_hitLength_iff (Y M b j : ℕ) (hM : 0 < M) (hb : b ≤ M) :
    j < hitLength Y M b ↔ b+M*j ≤ Y := by
  unfold hitLength
  rw [Nat.lt_iff_add_one_le,Nat.le_div_iff_mul_le hM,
    Nat.le_sub_iff_add_le (by omega : b ≤ Y+M)]
  constructor <;> intro h <;> nlinarith

theorem exists_positive_coordinate (M b n : ℕ) (_hM : 0 < M)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (hn : 1 ≤ n) (hres : Nat.ModEq M n b) :
    ∃ j : ℕ,n = b+M*j := by
  have hsub : Nat.ModEq M (n-1) (b-1) := by
    apply Nat.ModEq.add_left_cancel' 1
    simpa only [Nat.add_sub_of_le hn,Nat.add_sub_of_le hb1] using hres
  have hbsmall : b-1 < M := by omega
  have hrem : (n-1)%M = b-1 := by
    change (n-1)%M = (b-1)%M at hsub
    simpa only [Nat.mod_eq_of_lt hbsmall] using hsub
  refine ⟨(n-1)/M,?_⟩
  have heq := Nat.mod_add_div (n-1) M
  rw [hrem] at heq
  omega

theorem hitLength_error (Y M b : ℕ) (hM : 0 < M) (hb1 : 1 ≤ b) (hbM : b ≤ M) :
    |(hitLength Y M b : ℝ)-(Y : ℝ)/M| ≤ 1 := by
  have hsub : b ≤ Y+M := by omega
  have hdivision := Nat.mod_add_div (Y+M-b) M
  have hmod := Nat.mod_lt (Y+M-b) hM
  have heq : (((Y+M-b)%M : ℕ) : ℝ)+(M : ℝ)*hitLength Y M b = (Y : ℝ)+M-b := by
    simpa only [hitLength,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hsub] using
      congrArg (fun n : ℕ => (n : ℝ)) hdivision
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  have hrR : (((Y+M-b)%M : ℕ) : ℝ) < M := by exact_mod_cast hmod
  have hbR : (b : ℝ) ≤ M := by exact_mod_cast hbM
  have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hremR : (0 : ℝ) ≤ ((Y+M-b)%M : ℕ) := Nat.cast_nonneg _
  have hlo : (Y : ℝ)/M ≤ (hitLength Y M b : ℝ)+1 := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  have hhi : (hitLength Y M b : ℝ)-1 ≤ (Y : ℝ)/M := by
    apply (le_div_iff₀ hmR).mpr
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end ErdosInverseHits

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

theorem mem_modulusCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m n : ℕ) :
    n ∈ modulusCandidates Y small a m ↔ 1 ≤ n ∧ n ≤ Y ∧
      (∀ p ∈ m.primeFactors,n % p = a p % p) ∧ ∀ p ∈ small,n % p ≠ a p % p := by
  exact mem_residueCandidates

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_LargePrimeDeletion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped BigOperators

theorem divisibility_iff_modEq (a : ℤ) {q : ℕ} (hq : 0 < q) (i : ℕ) :
    (q : ℤ) ∣ a + i ↔ Nat.ModEq q i (divisibilityResidue a q) := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hr : ((divisibilityResidue a q : ℕ) : ℤ) = (-a) % q := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hqz))
  rw [← Int.natCast_modEq_iff, hr, Int.ModEq, Int.emod_emod, ← Int.ModEq,
    Int.modEq_iff_dvd]
  have heq : -a - (i : ℤ) = -(a + i) := by ring
  rw [heq, Int.dvd_neg]

theorem card_deletionCell_range (Y : ℕ) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    (deletionCell (Finset.range Y) a q).card =
      Y / q + if divisibilityResidue a q % q < Y % q then 1 else 0 := by
  classical
  unfold deletionCell
  simp_rw [divisibility_iff_modEq a hq]
  rw [← Nat.count_eq_card_filter_range]
  exact Nat.count_modEq_card Y hq (divisibilityResidue a q)

theorem coprime_iff_avoid_primeFactors {n : ℕ} (hn : 0 < n) (x : ℤ) :
    x.natAbs.Coprime n ↔ ∀ p ∈ n.primeFactors, ¬ (p : ℤ) ∣ x := by
  constructor
  · intro hc p hp hpx
    obtain ⟨hprime, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    have hpx' : p ∣ x.natAbs := Int.natCast_dvd.mp hpx
    exact hprime.not_dvd_one (by simpa only [hc.gcd_eq_one] using Nat.dvd_gcd hpx' hpn)
  · intro hav
    apply Nat.coprime_of_dvd
    intro p hp hpx hpn
    exact hav p (Nat.mem_primeFactors.mpr ⟨hp, hpn, ne_of_gt hn⟩)
      (Int.natCast_dvd.mpr hpx)

end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntervalBoundingSieve
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped BigOperators

theorem interval_multSum (A J P : ℕ) (hP : Squarefree P) (d : ℕ) :
    @BoundingSieve.multSum (intervalSieve A J P hP) d =
      ((LargePrimeDeletion.deletionCell (Finset.range J) (A : ℤ) d).card : ℝ) := by
  classical
  change (∑ n ∈ (Finset.range J).image (fun i => A + i),
    if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  · simp only [LargePrimeDeletion.deletionCell, ← Nat.cast_add,
      Int.natCast_dvd_natCast, Finset.sum_boole]
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

theorem interval_siftedSum (A J P : ℕ) (hP : Squarefree P) :
    @BoundingSieve.siftedSum (intervalSieve A J P hP) =
      ((LargePrimeDeletion.coprimeOffsets J P (A : ℤ)).card : ℝ) := by
  classical
  change (∑ n ∈ (Finset.range J).image (fun i => A + i),
    if P.Coprime n then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  · simp only [LargePrimeDeletion.coprimeOffsets, ← Nat.cast_add,
      Int.natAbs_natCast, Nat.coprime_comm, Finset.sum_boole]
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

theorem interval_rem_abs_le_one (A J P : ℕ) (hP : Squarefree P)
    {d : ℕ} (hd : 0 < d) :
    |@BoundingSieve.rem (intervalSieve A J P hP) d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : ((J / d : ℕ) : ℝ) ≤ (J : ℝ) / d := Nat.cast_div_le
  have hmod : ((J % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt J hd
  have heq : (J : ℝ) = ((J / d : ℕ) : ℝ) * d + (J % d : ℕ) := by
    exact_mod_cast (show J = J / d * d + J % d by simpa [Nat.mul_comm] using (Nat.div_add_mod J d).symm)
  have hupp : (J : ℝ) / d < ((J / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).mpr
    nlinarith
  have hcount := LargePrimeDeletion.card_deletionCell_range J (A : ℤ) hd
  change |@BoundingSieve.multSum (intervalSieve A J P hP) d -
    reciprocalDensity d * (J : ℝ)| ≤ 1
  rw [interval_multSum, reciprocalDensity_apply, inv_mul_eq_div]
  rw [hcount]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem coprime_count_le_upperMoebius (A J P : ℕ) (hP : Squarefree P)
    (muPlus : ℕ → ℝ) (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    ((LargePrimeDeletion.coprimeOffsets J P (A : ℤ)).card : ℝ) ≤
      (J : ℝ) * (∑ d ∈ P.divisors, muPlus d / d) +
        ∑ d ∈ P.divisors, |muPlus d| := by
  have hs := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius (s := intervalSieve A J P hP) muPlus hmu
  rw [interval_siftedSum] at hs
  have hmain : @BoundingSieve.mainSum (intervalSieve A J P hP) muPlus = ∑ d ∈ P.divisors, muPlus d / d := by
    change (∑ d ∈ P.divisors, muPlus d * reciprocalDensity d) = _
    simp only [reciprocalDensity_apply, div_eq_mul_inv]
  have herr : @BoundingSieve.errSum (intervalSieve A J P hP) muPlus ≤ ∑ d ∈ P.divisors, |muPlus d| := by
    change (∑ d ∈ P.divisors, |muPlus d| *
      |@BoundingSieve.rem (intervalSieve A J P hP) d|) ≤ _
    apply Finset.sum_le_sum
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors hd
    calc
      _ ≤ |muPlus d| * 1 := mul_le_mul_of_nonneg_left
        (interval_rem_abs_le_one A J P hP hdpos) (abs_nonneg _)
      _ = _ := mul_one _
  rw [hmain] at hs
  exact hs.trans (add_le_add le_rfl herr)

theorem exists_residue_translation (P : ℕ) (residue : ℕ → ℕ) :
    ∃ A : ℕ, ∀ p ∈ P.primeFactors, ∀ i : ℕ,
      p ∣ A + i ↔ i % p = residue p % p := by
  classical
  have hnz : ∀ p ∈ P.primeFactors, (id p : ℕ) ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpair : Set.Pairwise (P.primeFactors : Set ℕ)
      (fun p q => Nat.Coprime (id p) (id q)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  let t := Nat.chineseRemainderOfFinset (fun p => p - residue p % p) id
    P.primeFactors hnz hpair
  refine ⟨t.val, ?_⟩
  intro p hp i
  have hp0 := (Nat.prime_of_mem_primeFactors hp).pos
  have hsum : Nat.ModEq p (t.val + residue p) 0 := by
    have ht := (t.property p hp).add (Nat.mod_modEq (residue p) p).symm
    have ht' : Nat.ModEq p (t.val + residue p) p := by
      simpa only [id_eq, Nat.sub_add_cancel (Nat.mod_lt (residue p) hp0).le] using ht
    exact ht'.trans (dvd_refl p).modEq_zero_nat
  constructor
  · intro hdiv
    exact Nat.ModEq.add_left_cancel' t.val (hdiv.modEq_zero_nat.trans hsum.symm)
  · intro hres
    exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_left t.val hres).trans hsum)

theorem exists_residue_count_translation (J P : ℕ) (hP : 0 < P)
    (residue : ℕ → ℕ) :
    ∃ A : ℕ, residueAvoidingOffsets J P residue =
      LargePrimeDeletion.coprimeOffsets J P (A : ℤ) := by
  classical
  obtain ⟨A, hA⟩ := exists_residue_translation P residue
  refine ⟨A, ?_⟩
  ext i
  simp only [residueAvoidingOffsets, Finset.mem_filter, Finset.mem_range,
    LargePrimeDeletion.mem_coprimeOffsets,
    LargePrimeDeletion.coprime_iff_avoid_primeFactors hP, ← Nat.cast_add,
    Int.natCast_dvd_natCast]
  exact and_congr_right fun _ => forall₂_congr fun p hp => not_congr (hA p hp i).symm

theorem residue_count_le_upperMoebius (J P : ℕ) (hP : Squarefree P)
    (residue : ℕ → ℕ) (muPlus : ℕ → ℝ)
    (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    ((residueAvoidingOffsets J P residue).card : ℝ) ≤
      (J : ℝ) * (∑ d ∈ P.divisors, muPlus d / d) +
        ∑ d ∈ P.divisors, |muPlus d| := by
  obtain ⟨A, hA⟩ := exists_residue_count_translation J P (Nat.pos_of_ne_zero hP.ne_zero) residue
  rw [hA]
  exact coprime_count_le_upperMoebius A J P hP muPlus hmu

theorem cutoffSurvivors_card_le_upperMoebius (J z : ℕ) (residue : ℕ → ℕ)
    (muPlus : ℕ → ℝ) (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      (J : ℝ) * (∑ d ∈ (cutoffProduct z).divisors, muPlus d / d) +
        ∑ d ∈ (cutoffProduct z).divisors, |muPlus d| := by
  have hsets : LargePrimeDeletion.cutoffSurvivors J z residue =
      residueAvoidingOffsets J (cutoffProduct z) residue := by
    classical
    ext i
    simp only [LargePrimeDeletion.mem_cutoffSurvivors, residueAvoidingOffsets,
      Finset.mem_filter, Finset.mem_range, cutoffProduct_primeFactors,
      LargePrimeDeletion.mem_cutoffPrimes]
    tauto
  rw [hsets]
  exact residue_count_le_upperMoebius J (cutoffProduct z) (cutoffProduct_squarefree z)
    residue muPlus hmu

end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BonferroniBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniBlocks

open scoped BigOperators

theorem alternatingChoose_zero (m : ℕ) : alternatingChoose m 0 = 1 := by
  induction m with
  | zero => simp [alternatingChoose]
  | succ m ih =>
      unfold alternatingChoose at *
      rw [Finset.sum_range_succ, ih]
      simp

theorem alternatingChoose_succ (m n : ℕ) :
    alternatingChoose m (n + 1) = (-1 : ℝ) ^ m * n.choose m := by
  unfold alternatingChoose
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := m))

theorem alternatingChoose_even_nonneg (m n : ℕ) : 0 ≤ alternatingChoose (2 * m) n := by
  cases n with
  | zero => rw [alternatingChoose_zero]; norm_num
  | succ n =>
      rw [alternatingChoose_succ]
      simp only [pow_mul, neg_one_sq, one_pow, one_mul]
      exact Nat.cast_nonneg _

theorem alternatingChoose_bounds (m n : ℕ) :
    alternatingChoose (2 * m + 1) n ≤ (if n = 0 then 1 else 0 : ℝ) ∧
      (if n = 0 then 1 else 0 : ℝ) ≤ alternatingChoose (2 * m) n := by
  cases n with
  | zero => simp only [alternatingChoose_zero, ite_true, if_true, le_refl, and_self]
  | succ n =>
      rw [alternatingChoose_succ, alternatingChoose_succ]
      simp only [Nat.succ_ne_zero, ite_false, if_false, pow_add, pow_mul, neg_one_sq, one_pow,
        pow_one, one_mul, neg_mul]
      constructor
      · exact neg_nonpos.mpr (Nat.cast_nonneg _)
      · exact Nat.cast_nonneg _

theorem alternatingChoose_gap (m n : ℕ) :
    alternatingChoose (2 * m) n - alternatingChoose (2 * m + 1) n =
      (n.choose (2 * m + 1) : ℝ) := by
  unfold alternatingChoose
  rw [Finset.sum_range_succ (n := 2 * m + 1)]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  ring

theorem sum_intersectionValue_eq_choose (P : Finset ℕ) (hit : ℕ → Prop) (r : ℕ) :
    (∑ T ∈ P.powersetCard r, intersectionValue T hit) =
      ((hitSet P hit).card.choose r : ℝ) := by
  classical
  have hsets : (P.powersetCard r).filter (fun T => ∀ p ∈ T, hit p) =
      (hitSet P hit).powersetCard r := by
    ext T
    simp only [hitSet, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hTP, hcard⟩, hhit⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hTP hp, hhit p hp⟩, hcard⟩
    · rintro ⟨hT, hcard⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hT hp)).1, hcard⟩,
        fun p hp => (Finset.mem_filter.mp (hT hp)).2⟩
  unfold intersectionValue
  rw [Finset.sum_boole, hsets, Finset.card_powersetCard]

theorem coefficientPolynomial_eq_alternatingChoose (m : ℕ) (P : Finset ℕ)
    (hit : ℕ → Prop) :
    coefficientPolynomial m P hit = alternatingChoose m (hitSet P hit).card := by
  unfold coefficientPolynomial alternatingChoose
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_intersectionValue_eq_choose]

theorem survives_eq_zero_count (P : Finset ℕ) (hit : ℕ → Prop) :
    survives P hit = (if (hitSet P hit).card = 0 then 1 else 0 : ℝ) := by
  classical
  unfold survives
  have heq : (∀ p ∈ P, ¬ hit p) ↔ (hitSet P hit).card = 0 := by
    rw [hitSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [heq]

theorem coefficientPolynomial_bounds (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) :
    coefficientPolynomial (2 * m + 1) P hit ≤ survives P hit ∧
      survives P hit ≤ coefficientPolynomial (2 * m) P hit := by
  rw [coefficientPolynomial_eq_alternatingChoose, coefficientPolynomial_eq_alternatingChoose,
    survives_eq_zero_count]
  exact alternatingChoose_bounds m _

theorem coefficientPolynomial_even_nonneg (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) :
    0 ≤ coefficientPolynomial (2 * m) P hit := by
  rw [coefficientPolynomial_eq_alternatingChoose]
  exact alternatingChoose_even_nonneg _ _

theorem coefficientPolynomial_gap (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) :
    coefficientPolynomial (2 * m) P hit - coefficientPolynomial (2 * m + 1) P hit =
      (((hitSet P hit).card).choose (2 * m + 1) : ℝ) := by
  rw [coefficientPolynomial_eq_alternatingChoose, coefficientPolynomial_eq_alternatingChoose]
  exact alternatingChoose_gap _ _

theorem coefficientPolynomial_eq_one_of_no_hits (m : ℕ) (P : Finset ℕ)
    (hit : ℕ → Prop) (h : ∀ p ∈ P, ¬ hit p) : coefficientPolynomial m P hit = 1 := by
  classical
  have hset : hitSet P hit = ∅ := Finset.filter_eq_empty_iff.mpr h
  rw [coefficientPolynomial_eq_alternatingChoose, hset, Finset.card_empty,
    alternatingChoose_zero]

theorem block_bounds (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) :
    blockLower B blocks orders hit ≤ survives (B.biUnion blocks) hit ∧
      survives (B.biUnion blocks) hit ≤ blockUpper B blocks orders hit := by
  classical
  have hUpperNonneg : 0 ≤ blockUpper B blocks orders hit :=
    Finset.prod_nonneg fun j _ => coefficientPolynomial_even_nonneg _ _ _
  have hEraseNonneg : ∀ j, 0 ≤ ∏ i ∈ B.erase j,
      coefficientPolynomial (2 * orders i) (blocks i) hit := by
    intro j
    exact Finset.prod_nonneg fun i _ => coefficientPolynomial_even_nonneg _ _ _
  have hCorrectionNonneg : ∀ j ∈ B, 0 ≤
      (coefficientPolynomial (2 * orders j) (blocks j) hit -
        coefficientPolynomial (2 * orders j + 1) (blocks j) hit) *
      ∏ i ∈ B.erase j, coefficientPolynomial (2 * orders i) (blocks i) hit := by
    intro j _
    rw [coefficientPolynomial_gap]
    exact mul_nonneg (Nat.cast_nonneg _) (hEraseNonneg j)
  by_cases hgood : ∀ j ∈ B, ∀ p ∈ blocks j, ¬ hit p
  · have hpoly : ∀ j ∈ B, ∀ m,
        coefficientPolynomial m (blocks j) hit = 1 := by
      intro j hj m
      exact coefficientPolynomial_eq_one_of_no_hits m (blocks j) hit (hgood j hj)
    have hupper : blockUpper B blocks orders hit = 1 := by
      unfold blockUpper
      apply Finset.prod_eq_one
      intro j hj
      exact hpoly j hj _
    have hcorr : blockCorrection B blocks orders hit = 0 := by
      unfold blockCorrection
      apply Finset.sum_eq_zero
      intro j hj
      rw [hpoly j hj _, hpoly j hj _, sub_self, zero_mul]
    have hsurv : survives (B.biUnion blocks) hit = 1 := by
      unfold survives
      apply ite_eq_left
      intro p hp
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
      exact hgood j hj p hpj
    simp only [blockLower, hupper, hcorr, hsurv, sub_zero, le_refl, and_self]
  · have hbad : ∃ j ∈ B, ∃ p ∈ blocks j, hit p := by
      simpa only [not_forall, Classical.not_imp, not_not, exists_prop] using hgood
    obtain ⟨j, hj, p, hp, hhit⟩ := hbad
    have hsurvj : survives (blocks j) hit = 0 := by
      unfold survives
      exact ite_eq_right (fun h => h p hp hhit)
    have hsurv : survives (B.biUnion blocks) hit = 0 := by
      unfold survives
      exact ite_eq_right (fun h => h p (Finset.mem_biUnion.mpr ⟨j, hj, hp⟩) hhit)
    have hLj : coefficientPolynomial (2 * orders j + 1) (blocks j) hit ≤ 0 := by
      simpa only [hsurvj] using (coefficientPolynomial_bounds (orders j) (blocks j) hit).1
    have hProdLe : blockUpper B blocks orders hit ≤
        (coefficientPolynomial (2 * orders j) (blocks j) hit -
          coefficientPolynomial (2 * orders j + 1) (blocks j) hit) *
        ∏ i ∈ B.erase j, coefficientPolynomial (2 * orders i) (blocks i) hit := by
      unfold blockUpper
      rw [← Finset.mul_prod_erase B _ hj]
      exact mul_le_mul_of_nonneg_right (by linarith) (hEraseNonneg j)
    have hSumLe : blockUpper B blocks orders hit ≤ blockCorrection B blocks orders hit :=
      hProdLe.trans (Finset.single_le_sum hCorrectionNonneg hj)
    rw [hsurv]
    exact ⟨sub_nonpos.mpr hSumLe, hUpperNonneg⟩

theorem weighted_block_bounds {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → α → Prop) :
    (∑ x ∈ C, weight x * blockLower B blocks orders (fun p => hit p x)) ≤
        ∑ x ∈ C, weight x * survives (B.biUnion blocks) (fun p => hit p x) ∧
      (∑ x ∈ C, weight x * survives (B.biUnion blocks) (fun p => hit p x)) ≤
        ∑ x ∈ C, weight x * blockUpper B blocks orders (fun p => hit p x) := by
  constructor
  · apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (block_bounds B blocks orders (fun p => hit p x)).1 (hweight x hx)
  · apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (block_bounds B blocks orders (fun p => hit p x)).2 (hweight x hx)

theorem coefficient_divisor_support (P : Finset ℕ) {v m r : ℕ}
    (hv : 1 ≤ v) (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v)
    (hr : r ≤ m) {T : Finset ℕ} (hT : T ∈ P.powersetCard r) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ v ^ m := by
  obtain ⟨hTP, hcard⟩ := Finset.mem_powersetCard.mp hT
  constructor
  · exact IntervalBoundingSieve.squarefree_primeSet_product T (fun p hp => hprime p (hTP hp))
  · calc
      (∏ p ∈ T, p) ≤ ∏ _p ∈ T, v := Finset.prod_le_prod' (fun p hp => hheight p (hTP hp))
      _ = v ^ r := by simp only [Finset.prod_const, hcard]
      _ ≤ v ^ m := Nat.pow_le_pow_right hv hr

end NumberTheoryLean.BonferroniBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_BonferroniDensity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped BigOperators

theorem elementarySum_nonneg (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) (k : ℕ) : 0 ≤ elementarySum P g k := by
  apply Finset.sum_nonneg
  intro T hT
  exact Finset.prod_nonneg fun p hp => hg p ((Finset.mem_powersetCard.mp hT).1 hp)

theorem elementarySum_insert (P : Finset ℕ) (g : ℕ → ℝ) {a : ℕ} (ha : a ∉ P) (k : ℕ) :
    elementarySum (insert a P) g (k + 1) =
      elementarySum P g (k + 1) + g a * elementarySum P g k := by
  classical
  have hdis : Disjoint (P.powersetCard (k + 1)) ((P.powersetCard k).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro T hT hTi
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hTi
    exact ha ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self a U))
  have hinj : Set.InjOn (insert a) (P.powersetCard k : Set (Finset ℕ)) := by
    intro T hT U hU hEq
    have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
    have haU : a ∉ U := fun h => ha ((Finset.mem_powersetCard.mp hU).1 h)
    have h := congrArg (fun S : Finset ℕ => S.erase a) hEq
    simpa only [Finset.erase_insert haT, Finset.erase_insert haU] using h
  unfold elementarySum
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdis, Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  exact Finset.prod_insert (fun haT => ha ((Finset.mem_powersetCard.mp hT).1 haT))

theorem factorial_mul_elementarySum_le (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) (k : ℕ) :
    (k.factorial : ℝ) * elementarySum P g k ≤ (∑ p ∈ P, g p) ^ k := by
  classical
  revert hg k
  induction P using Finset.induction_on with
  | empty =>
      intro _ k
      cases k with
      | zero => simp [elementarySum]
      | succ k =>
          have he : (∅ : Finset ℕ).powersetCard (k + 1) = ∅ :=
            Finset.powersetCard_eq_empty.mpr (by simp)
          simp only [elementarySum, he, Finset.sum_empty, mul_zero, zero_pow (Nat.succ_ne_zero k), le_refl]
  | @insert a P ha ih =>
      intro hg k
      have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a P)
      have hgP : ∀ p ∈ P, 0 ≤ g p := fun p hp => hg p (Finset.mem_insert_of_mem hp)
      have hsum : 0 ≤ ∑ p ∈ P, g p := Finset.sum_nonneg hgP
      cases k with
      | zero => simp
      | succ k =>
          rw [elementarySum_insert P g ha, Finset.sum_insert ha]
          have hi0 := ih hgP k
          have hi1 := ih hgP (k + 1)
          calc
            (((k + 1).factorial : ℕ) : ℝ) *
                (elementarySum P g (k + 1) + g a * elementarySum P g k) =
                (((k + 1).factorial : ℕ) : ℝ) * elementarySum P g (k + 1) +
                  ((k + 1 : ℕ) : ℝ) * g a * ((k.factorial : ℝ) * elementarySum P g k) := by
              rw [Nat.factorial_succ]
              push_cast
              ring
            _ ≤ (∑ p ∈ P, g p) ^ (k + 1) +
                ((k + 1 : ℕ) : ℝ) * g a * (∑ p ∈ P, g p) ^ k :=
              add_le_add hi1 (mul_le_mul_of_nonneg_left hi0 (by positivity))
            _ ≤ ((∑ p ∈ P, g p) + g a) ^ (k + 1) := by
              have h := pow_add_mul_le_add_pow hsum
                (show 0 ≤ 2 * (∑ p ∈ P, g p) + g a by positivity) (k + 1)
              simpa only [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using h
            _ = _ := by rw [add_comm]

theorem elementarySum_le_pow_div_factorial (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) {A : ℝ} (_hA : 0 ≤ A)
    (hsum : ∑ p ∈ P, g p ≤ A) (k : ℕ) :
    elementarySum P g k ≤ A ^ k / k.factorial := by
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos k)).mpr
  calc
    elementarySum P g k * (k.factorial : ℝ) =
        (k.factorial : ℝ) * elementarySum P g k := mul_comm _ _
    _ ≤ (∑ p ∈ P, g p) ^ k := factorial_mul_elementarySum_le P g hg k
    _ ≤ A ^ k := pow_le_pow_left₀ (Finset.sum_nonneg hg) hsum k

theorem elementarySum_le_exponential (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) {A : ℝ} (hA : 0 ≤ A)
    (hsum : ∑ p ∈ P, g p ≤ A) (k : ℕ) :
    elementarySum P g k ≤ Real.exp (2 * A) / (2 : ℝ) ^ k := by
  calc
    elementarySum P g k ≤ A ^ k / k.factorial := elementarySum_le_pow_div_factorial P g hg hA hsum k
    _ = ((2 * A) ^ k / k.factorial) / (2 : ℝ) ^ k := by
      rw [mul_pow]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (Real.pow_div_factorial_le_exp (2 * A) (by positivity) k) (by positivity)

theorem exp_neg_three_mul_le_eulerProduct (P : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg2 : ∀ p ∈ P, g p ≤ 2 / 3)
    {A : ℝ} (hsum : ∑ p ∈ P, g p ≤ A) :
    Real.exp (-3 * A) ≤ ∏ p ∈ P, (1 - g p) := by
  have hpoint : ∀ p ∈ P, Real.exp (-3 * g p) ≤ 1 - g p := by
    intro p hp
    have h0 := hg0 p hp
    have h2 := hg2 p hp
    have hpos : 0 < 1 - g p := by linarith
    have hinv : (1 - g p)⁻¹ ≤ 1 + 3 * g p := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      nlinarith [mul_nonneg h0 (show 0 ≤ 2 - 3 * g p by linarith)]
    have hlog : -3 * g p ≤ Real.log (1 - g p) := by
      have h := Real.one_sub_inv_le_log_of_pos hpos
      linarith
    exact (Real.le_log_iff_exp_le hpos).mp hlog
  calc
    Real.exp (-3 * A) ≤ Real.exp (-3 * ∑ p ∈ P, g p) := Real.exp_le_exp.mpr (by linarith)
    _ = ∏ p ∈ P, Real.exp (-3 * g p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) hpoint

theorem relative_elementarySum_le_exponential (P : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg2 : ∀ p ∈ P, g p ≤ 2 / 3)
    {A : ℝ} (hA : 0 ≤ A) (hsum : ∑ p ∈ P, g p ≤ A) (k : ℕ) :
    elementarySum P g k / (∏ p ∈ P, (1 - g p)) ≤ Real.exp (5 * A) / (2 : ℝ) ^ k := by
  have hEuler := exp_neg_three_mul_le_eulerProduct P g hg0 hg2 hsum
  have hpos : 0 < ∏ p ∈ P, (1 - g p) := (Real.exp_pos _).trans_le hEuler
  have hexp : Real.exp (2 * A) / Real.exp (-3 * A) = Real.exp (5 * A) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ (Real.exp (2 * A) / (2 : ℝ) ^ k) / (∏ p ∈ P, (1 - g p)) :=
      div_le_div_of_nonneg_right (elementarySum_le_exponential P g hg0 hA hsum k) hpos.le
    _ ≤ (Real.exp (2 * A) / (2 : ℝ) ^ k) / Real.exp (-3 * A) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hEuler
    _ = (Real.exp (2 * A) / Real.exp (-3 * A)) / (2 : ℝ) ^ k := by ring
    _ = _ := by rw [hexp]

theorem prime_density_le_two_thirds (P : Finset ℕ) (g : ℕ → ℝ)
    (hprime : ∀ p ∈ P, p.Prime) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) : ∀ p ∈ P, g p ≤ 2 / 3 := by
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    have h := htwo hp
    linarith
  · have hp3 : 3 ≤ p := by have := (hprime p hp).two_le; omega
    apply (hdim p hp).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp3)

theorem densityPolynomial_succ (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial (m + 1) P g = densityPolynomial m P g +
      (-1 : ℝ) ^ (m + 1) * elementarySum P g (m + 1) := by
  exact Finset.sum_range_succ _ _

theorem densityPolynomial_empty (m : ℕ) (g : ℕ → ℝ) :
    densityPolynomial m ∅ g = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [densityPolynomial_succ, ih]
      have he : (∅ : Finset ℕ).powersetCard (m + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp only [elementarySum, he, Finset.sum_empty, mul_zero, add_zero]

theorem densityPolynomial_insert (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    {a : ℕ} (ha : a ∉ P) :
    densityPolynomial (m + 1) (insert a P) g =
      densityPolynomial (m + 1) P g - g a * densityPolynomial m P g := by
  induction m with
  | zero =>
      rw [densityPolynomial_succ, densityPolynomial_succ,
        elementarySum_insert P g ha]
      simp only [densityPolynomial_zero, elementarySum_zero, mul_one]
      ring
  | succ m ih =>
      rw [densityPolynomial_succ (m + 1) (insert a P), ih,
        elementarySum_insert P g ha (m + 1), densityPolynomial_succ (m + 1) P,
        densityPolynomial_succ m P, pow_succ (-1 : ℝ) (m + 1)]
      ring

theorem densityPolynomial_bounds (P : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p ≤ 1) (m : ℕ) :
    densityPolynomial (2 * m + 1) P g ≤ (∏ p ∈ P, (1 - g p)) ∧
      (∏ p ∈ P, (1 - g p)) ≤ densityPolynomial (2 * m) P g := by
  classical
  revert hg0 hg1 m
  induction P using Finset.induction_on with
  | empty => intro _ _ m; simp only [densityPolynomial_empty, Finset.prod_empty, le_refl, and_self]
  | @insert a P ha ih =>
      intro hg0 hg1 m
      have hga := hg0 a (Finset.mem_insert_self a P)
      have hgP0 : ∀ p ∈ P, 0 ≤ g p := fun p hp => hg0 p (Finset.mem_insert_of_mem hp)
      have hgP1 : ∀ p ∈ P, g p ≤ 1 := fun p hp => hg1 p (Finset.mem_insert_of_mem hp)
      have hbase := ih hgP0 hgP1 m
      constructor
      · rw [densityPolynomial_insert (2 * m) P g ha, Finset.prod_insert ha]
        nlinarith [mul_nonneg hga (sub_nonneg.mpr hbase.2)]
      · cases m with
        | zero =>
            simp only [Nat.mul_zero, densityPolynomial_zero]
            apply Finset.prod_le_one
            · intro p hp
              exact sub_nonneg.mpr (hg1 p hp)
            · intro p hp
              linarith [hg0 p hp]
        | succ m =>
            have hlow := (ih hgP0 hgP1 m).1
            have hupp := (ih hgP0 hgP1 (m + 1)).2
            have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
            rw [hidx, densityPolynomial_insert (2 * m + 1) P g ha, Finset.prod_insert ha]
            rw [hidx] at hupp
            nlinarith [mul_nonneg hga (sub_nonneg.mpr hlow)]

theorem densityPolynomial_gap (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial (2 * m) P g - densityPolynomial (2 * m + 1) P g =
      elementarySum P g (2 * m + 1) := by
  rw [densityPolynomial_succ]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  ring

theorem densityPolynomial_relative_error (P : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg2 : ∀ p ∈ P, g p ≤ 2 / 3)
    {A : ℝ} (hA : 0 ≤ A) (hsum : ∑ p ∈ P, g p ≤ A) (m : ℕ) :
    |densityPolynomial (2 * m) P g / (∏ p ∈ P, (1 - g p)) - 1| ≤
        Real.exp (5 * A) / (2 : ℝ) ^ (2 * m + 1) ∧
      |densityPolynomial (2 * m + 1) P g / (∏ p ∈ P, (1 - g p)) - 1| ≤
        Real.exp (5 * A) / (2 : ℝ) ^ (2 * m + 1) := by
  have hEuler := exp_neg_three_mul_le_eulerProduct P g hg0 hg2 hsum
  have hpos : 0 < ∏ p ∈ P, (1 - g p) := (Real.exp_pos _).trans_le hEuler
  have hb := densityPolynomial_bounds P g hg0 (fun p hp => by linarith [hg2 p hp]) m
  have hgap := densityPolynomial_gap m P g
  have htail := relative_elementarySum_le_exponential P g hg0 hg2 hA hsum (2 * m + 1)
  have hUP : 0 ≤ densityPolynomial (2 * m) P g / (∏ p ∈ P, (1 - g p)) - 1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hpos).mpr (by simpa using hb.2)
  have hLP : densityPolynomial (2 * m + 1) P g / (∏ p ∈ P, (1 - g p)) - 1 ≤ 0 := by
    apply sub_nonpos.mpr
    exact (div_le_iff₀ hpos).mpr (by simpa using hb.1)
  constructor
  · rw [abs_of_nonneg hUP]
    apply le_trans ?_ htail
    have hEq : densityPolynomial (2 * m) P g / (∏ p ∈ P, (1 - g p)) - 1 =
        (densityPolynomial (2 * m) P g - (∏ p ∈ P, (1 - g p))) /
          (∏ p ∈ P, (1 - g p)) := by
      field_simp
    rw [hEq]
    exact (div_le_div_iff_of_pos_right hpos).mpr (by linarith)
  · rw [abs_of_nonpos hLP]
    apply le_trans ?_ htail
    have hEq : -(densityPolynomial (2 * m + 1) P g / (∏ p ∈ P, (1 - g p)) - 1) =
        ((∏ p ∈ P, (1 - g p)) - densityPolynomial (2 * m + 1) P g) /
          (∏ p ∈ P, (1 - g p)) := by
      field_simp
      ring
    rw [hEq]
    exact (div_le_div_iff_of_pos_right hpos).mpr (by linarith)

theorem densityPolynomial_eq_momentPolynomial (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial m P g = BonferroniBlocks.momentPolynomial m P (fun T => ∏ p ∈ T, g p) := rfl

end NumberTheoryLean.BonferroniDensity

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_DisjointBlockExpansion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped BigOperators

theorem selectedUnion_subset {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} (hc : choice ∈ blockChoices B blocks) :
    selectedUnion B choice ⊆ B.biUnion blocks := by
  classical
  intro p hp
  obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j.1, j.2, (mem_blockChoices.mp hc j.1 j.2) hpj⟩

theorem selectedUnion_inter_block {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    {choice : ∀ j ∈ B, Finset ℕ} (hc : choice ∈ blockChoices B blocks)
    (j : ℕ) (hj : j ∈ B) : selectedUnion B choice ∩ blocks j = choice j hj := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpu, hpj⟩ := Finset.mem_inter.mp hp
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hpu
    by_cases hij : i.1 = j
    · subst j
      exact hpi
    · exact False.elim ((Finset.disjoint_left.mp (hdis i.2 hj hij))
        ((mem_blockChoices.mp hc i.1 i.2) hpi) hpj)
  · intro hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
      ⟨⟨j, hj⟩, Finset.mem_attach _ _, hp⟩, (mem_blockChoices.mp hc j hj) hp⟩

theorem intersectionChoices_mem (B : Finset ℕ) (blocks : ℕ → Finset ℕ) (T : Finset ℕ) :
    intersectionChoices B blocks T ∈ blockChoices B blocks := by
  apply mem_blockChoices.mpr
  intro j _
  exact Finset.inter_subset_right

theorem selectedUnion_intersectionChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {T : Finset ℕ} (hT : T ⊆ B.biUnion blocks) :
    selectedUnion B (intersectionChoices B blocks T) = T := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpj).1
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp (hT hp)
    exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, Finset.mem_inter.mpr ⟨hp, hpj⟩⟩

theorem sum_subsets_product (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (F : ℕ → Finset ℕ → ℝ) :
    (∑ T ∈ (B.biUnion blocks).powerset, ∏ j ∈ B, F j (T ∩ blocks j)) =
      ∏ j ∈ B, ∑ T ∈ (blocks j).powerset, F j T := by
  classical
  symm
  rw [Finset.prod_sum]
  apply Finset.sum_bij (fun choice _ => selectedUnion B choice)
  · intro choice hc
    exact Finset.mem_powerset.mpr (selectedUnion_subset hc)
  · intro choice hc other ho heq
    funext j hj
    rw [← selectedUnion_inter_block hdis hc j hj, heq,
      selectedUnion_inter_block hdis ho j hj]
  · intro T hT
    exact ⟨intersectionChoices B blocks T, intersectionChoices_mem B blocks T,
      selectedUnion_intersectionChoices (Finset.mem_powerset.mp hT)⟩
  · intro choice hc
    conv_rhs => rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro j _
    rw [selectedUnion_inter_block hdis hc j.1 j.2]

theorem truncatedCoefficient_sum (m : ℕ) (P : Finset ℕ) (F : Finset ℕ → ℝ) :
    (∑ T ∈ P.powerset, truncatedCoefficient m T * F T) =
      BonferroniBlocks.momentPolynomial m P F := by
  classical
  let S := P.powerset.filter fun T => T.card ≤ m
  have hmap : ∀ T ∈ S, T.card ∈ Finset.range (m + 1) := by
    intro T hT
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hT).2)
  calc
    _ = ∑ T ∈ S, (-1 : ℝ) ^ T.card * F T := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      unfold truncatedCoefficient
      split_ifs <;> simp
    _ = ∑ r ∈ Finset.range (m + 1), ∑ T ∈ S.filter (fun T => T.card = r),
        (-1 : ℝ) ^ T.card * F T :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = _ := by
      unfold BonferroniBlocks.momentPolynomial
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hsets : S.filter (fun T => T.card = r) = P.powersetCard r := by
        ext T
        simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hTP, _⟩, hcard⟩
          exact ⟨hTP, hcard⟩
        · rintro ⟨hTP, hcard⟩
          exact ⟨⟨hTP, by omega⟩, hcard⟩
      rw [hsets, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [(Finset.mem_powersetCard.mp hT).2]

theorem truncatedCoefficient_evaluation (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) :
    (∑ T ∈ P.powerset, truncatedCoefficient m T * BonferroniBlocks.intersectionValue T hit) =
      BonferroniBlocks.coefficientPolynomial m P hit :=
  truncatedCoefficient_sum m P (fun T => BonferroniBlocks.intersectionValue T hit)

theorem layerCoefficient_evaluation (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) :
    (∑ T ∈ P.powerset, layerCoefficient m T * BonferroniBlocks.intersectionValue T hit) =
      (((BonferroniBlocks.hitSet P hit).card).choose m : ℝ) := by
  classical
  calc
    _ = ∑ T ∈ P.powersetCard m, BonferroniBlocks.intersectionValue T hit := by
      rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      unfold layerCoefficient
      split_ifs <;> simp
    _ = _ := BonferroniBlocks.sum_intersectionValue_eq_choose P hit m

theorem intersectionValue_eq_product {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {T : Finset ℕ} (hT : T ⊆ B.biUnion blocks) (hit : ℕ → Prop) :
    BonferroniBlocks.intersectionValue T hit =
      ∏ j ∈ B, BonferroniBlocks.intersectionValue (T ∩ blocks j) hit := by
  classical
  by_cases hhit : ∀ p ∈ T, hit p
  · have hlocal : ∀ j ∈ B, BonferroniBlocks.intersectionValue (T ∩ blocks j) hit = 1 := by
      intro j _
      apply ite_eq_left
      intro p hp
      exact hhit p (Finset.mem_inter.mp hp).1
    unfold BonferroniBlocks.intersectionValue
    rw [ite_eq_left hhit]
    symm
    exact Finset.prod_eq_one hlocal
  · have hbad : ∃ p ∈ T, ¬ hit p := by
      simpa only [not_forall, Classical.not_imp, exists_prop] using hhit
    obtain ⟨p, hp, hnot⟩ := hbad
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp (hT hp)
    have hlocal : BonferroniBlocks.intersectionValue (T ∩ blocks j) hit = 0 :=
      ite_eq_right (fun h => hnot (h p (Finset.mem_inter.mpr ⟨hp, hpj⟩)))
    rw [BonferroniBlocks.intersectionValue, ite_eq_right hhit]
    symm
    exact Finset.prod_eq_zero hj hlocal

theorem globalCoefficient_evaluation (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (localCoeff : ℕ → Finset ℕ → ℝ) (hit : ℕ → Prop) :
    (∑ T ∈ (B.biUnion blocks).powerset,
      globalCoefficient B blocks localCoeff T * BonferroniBlocks.intersectionValue T hit) =
      ∏ j ∈ B, ∑ T ∈ (blocks j).powerset, localCoeff j T * BonferroniBlocks.intersectionValue T hit := by
  calc
    _ = ∑ T ∈ (B.biUnion blocks).powerset,
        ∏ j ∈ B, localCoeff j (T ∩ blocks j) * BonferroniBlocks.intersectionValue (T ∩ blocks j) hit := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [intersectionValue_eq_product (Finset.mem_powerset.mp hT), Finset.prod_mul_distrib]
      rfl
    _ = _ := sum_subsets_product B blocks hdis
      (fun j T => localCoeff j T * BonferroniBlocks.intersectionValue T hit)

theorem upperCoefficient_evaluation (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (hit : ℕ → Prop) :
    (∑ T ∈ (B.biUnion blocks).powerset,
      upperCoefficient B blocks orders T * BonferroniBlocks.intersectionValue T hit) =
      BonferroniBlocks.blockUpper B blocks orders hit := by
  unfold upperCoefficient
  rw [globalCoefficient_evaluation B blocks hdis]
  simp_rw [truncatedCoefficient_evaluation]
  rfl

theorem correctionCoefficient_evaluation (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (hit : ℕ → Prop) (j : ℕ) (hj : j ∈ B) :
    (∑ T ∈ (B.biUnion blocks).powerset,
      correctionCoefficient B blocks orders j T * BonferroniBlocks.intersectionValue T hit) =
      (BonferroniBlocks.coefficientPolynomial (2 * orders j) (blocks j) hit -
        BonferroniBlocks.coefficientPolynomial (2 * orders j + 1) (blocks j) hit) *
      ∏ i ∈ B.erase j, BonferroniBlocks.coefficientPolynomial (2 * orders i) (blocks i) hit := by
  classical
  unfold correctionCoefficient
  rw [globalCoefficient_evaluation B blocks hdis]
  rw [← Finset.mul_prod_erase B _ hj]
  simp only [ite_true, if_true]
  rw [layerCoefficient_evaluation, ← BonferroniBlocks.coefficientPolynomial_gap]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  simp only [ite_eq_right hij]
  exact truncatedCoefficient_evaluation _ _ _

theorem lowerCoefficient_evaluation (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (hit : ℕ → Prop) :
    (∑ T ∈ (B.biUnion blocks).powerset,
      lowerCoefficient B blocks orders T * BonferroniBlocks.intersectionValue T hit) =
      BonferroniBlocks.blockLower B blocks orders hit := by
  unfold lowerCoefficient BonferroniBlocks.blockLower BonferroniBlocks.blockCorrection
  simp_rw [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_comm,
    upperCoefficient_evaluation B blocks hdis]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [sub_mul] using correctionCoefficient_evaluation B blocks hdis orders hit j hj

theorem truncatedCoefficient_abs_le (m : ℕ) (T : Finset ℕ) :
    |truncatedCoefficient m T| ≤ 1 := by
  unfold truncatedCoefficient
  split_ifs <;> simp

theorem layerCoefficient_abs_le (m : ℕ) (T : Finset ℕ) :
    |layerCoefficient m T| ≤ 1 := by
  unfold layerCoefficient
  split_ifs <;> simp

theorem globalCoefficient_abs_le (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (localCoeff : ℕ → Finset ℕ → ℝ) (T : Finset ℕ)
    (hlocal : ∀ j ∈ B, |localCoeff j (T ∩ blocks j)| ≤ 1) :
    |globalCoefficient B blocks localCoeff T| ≤ 1 := by
  unfold globalCoefficient
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hlocal

theorem upperCoefficient_abs_le (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : |upperCoefficient B blocks orders T| ≤ 1 :=
  globalCoefficient_abs_le B blocks _ T (fun _ _ => truncatedCoefficient_abs_le _ _)

theorem correctionCoefficient_abs_le (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (j : ℕ) (T : Finset ℕ) : |correctionCoefficient B blocks orders j T| ≤ 1 := by
  apply globalCoefficient_abs_le
  intro i _
  split_ifs
  · exact layerCoefficient_abs_le _ _
  · exact truncatedCoefficient_abs_le _ _

theorem correctionCoefficient_own_card {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {j : ℕ} {T : Finset ℕ} (hj : j ∈ B)
    (hc : correctionCoefficient B blocks orders j T ≠ 0) :
    (T ∩ blocks j).card = 2 * orders j + 1 := by
  have h := Finset.prod_ne_zero_iff.mp hc j hj
  simpa only [ite_true, if_true, layerCoefficient_ne_zero_iff] using h

theorem correctionCoefficient_other_card {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {i j : ℕ} {T : Finset ℕ} (hi : i ∈ B) (hij : i ≠ j)
    (hc : correctionCoefficient B blocks orders j T ≠ 0) :
    (T ∩ blocks i).card ≤ 2 * orders i := by
  have h := Finset.prod_ne_zero_iff.mp hc i hi
  simpa only [ite_eq_right hij, truncatedCoefficient_ne_zero_iff] using h

theorem correctionCoefficient_disjoint {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {i j : ℕ} {T : Finset ℕ} (hi : i ∈ B) (_hj : j ∈ B) (hij : i ≠ j)
    (hiC : correctionCoefficient B blocks orders i T ≠ 0) :
    correctionCoefficient B blocks orders j T = 0 := by
  by_contra hjC
  have hown := correctionCoefficient_own_card hi hiC
  have hother := correctionCoefficient_other_card hi hij hjC
  omega

theorem upperCoefficient_zero_of_correction {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {j : ℕ} {T : Finset ℕ} (hj : j ∈ B)
    (hc : correctionCoefficient B blocks orders j T ≠ 0) : upperCoefficient B blocks orders T = 0 := by
  have hcard := correctionCoefficient_own_card hj hc
  apply Finset.prod_eq_zero hj
  change (if (T ∩ blocks j).card ≤ 2 * orders j then (-1 : ℝ) ^ (T ∩ blocks j).card else 0) = 0
  rw [ite_eq_right (by omega)]

theorem lowerCoefficient_abs_le (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : |lowerCoefficient B blocks orders T| ≤ 1 := by
  classical
  by_cases hactive : ∃ j ∈ B, correctionCoefficient B blocks orders j T ≠ 0
  · obtain ⟨j, hj, hjC⟩ := hactive
    have hsum : (∑ i ∈ B, correctionCoefficient B blocks orders i T) =
        correctionCoefficient B blocks orders j T := by
      apply Finset.sum_eq_single_of_mem j hj
      intro i hi hij
      exact correctionCoefficient_disjoint hj hi hij.symm hjC
    rw [lowerCoefficient, upperCoefficient_zero_of_correction hj hjC, hsum, zero_sub, abs_neg]
    exact correctionCoefficient_abs_le _ _ _ _ _
  · have hsum : (∑ j ∈ B, correctionCoefficient B blocks orders j T) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_contra hjC
      exact hactive ⟨j, hj, hjC⟩
    rw [lowerCoefficient, hsum, sub_zero]
    exact upperCoefficient_abs_le _ _ _ _

theorem prod_inter_blocks {M : Type*} [CommMonoid M] (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    {T : Finset ℕ} (hT : T ⊆ B.biUnion blocks) (g : ℕ → M) :
    (∏ p ∈ T, g p) = ∏ j ∈ B, ∏ p ∈ T ∩ blocks j, g p := by
  classical
  have hparts : (B : Set ℕ).PairwiseDisjoint (fun j => T ∩ blocks j) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hUnion : B.biUnion (fun j => T ∩ blocks j) = T := by
    rw [← Finset.inter_biUnion, Finset.inter_eq_left.mpr hT]
  calc
    (∏ p ∈ T, g p) = ∏ p ∈ B.biUnion (fun j => T ∩ blocks j), g p := by rw [hUnion]
    _ = _ := Finset.prod_biUnion hparts

theorem globalCoefficient_density (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (localCoeff : ℕ → Finset ℕ → ℝ) (g : ℕ → ℝ) :
    (∑ T ∈ (B.biUnion blocks).powerset, globalCoefficient B blocks localCoeff T * ∏ p ∈ T, g p) =
      ∏ j ∈ B, ∑ T ∈ (blocks j).powerset, localCoeff j T * ∏ p ∈ T, g p := by
  calc
    _ = ∑ T ∈ (B.biUnion blocks).powerset,
        ∏ j ∈ B, localCoeff j (T ∩ blocks j) * ∏ p ∈ T ∩ blocks j, g p := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [prod_inter_blocks B blocks hdis (Finset.mem_powerset.mp hT), Finset.prod_mul_distrib]
      rfl
    _ = _ := sum_subsets_product B blocks hdis (fun j T => localCoeff j T * ∏ p ∈ T, g p)

theorem upperCoefficient_density (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (g : ℕ → ℝ) :
    (∑ T ∈ (B.biUnion blocks).powerset, upperCoefficient B blocks orders T * ∏ p ∈ T, g p) =
      ∏ j ∈ B, BonferroniDensity.densityPolynomial (2 * orders j) (blocks j) g := by
  unfold upperCoefficient
  rw [globalCoefficient_density B blocks hdis]
  simp_rw [truncatedCoefficient_sum, ← BonferroniDensity.densityPolynomial_eq_momentPolynomial]

theorem weighted_coefficient_expansion {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (Q : Finset ℕ) (coeff : Finset ℕ → ℝ) :
    (∑ T ∈ Q.powerset, coeff T * BonferroniBlocks.intersectionMass C weight hit T) =
      ∑ x ∈ C, weight x * ∑ T ∈ Q.powerset, coeff T * BonferroniBlocks.intersectionValue T (fun p => hit p x) := by
  unfold BonferroniBlocks.intersectionMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem global_main_remainder {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (Q : Finset ℕ) (coeff : Finset ℕ → ℝ) (X : ℝ) (g : ℕ → ℝ) :
    (∑ T ∈ Q.powerset, coeff T * BonferroniBlocks.intersectionMass C weight hit T) =
      X * (∑ T ∈ Q.powerset, coeff T * ∏ p ∈ T, g p) +
        ∑ T ∈ Q.powerset, coeff T * BonferroniBlocks.intersectionRemainder C weight hit X g T := by
  unfold BonferroniBlocks.intersectionRemainder
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem supported_remainder_bound (Q : Finset ℕ) (coeff E : Finset ℕ → ℝ)
    (hc : ∀ T ∈ Q.powerset, |coeff T| ≤ 1) :
    |∑ T ∈ Q.powerset, coeff T * E T| ≤
      ∑ T ∈ Q.powerset.filter (fun T => coeff T ≠ 0), |E T| := by
  classical
  have hreindex : (∑ T ∈ Q.powerset, coeff T * E T) =
      ∑ T ∈ Q.powerset.filter (fun T => coeff T ≠ 0), coeff T * E T := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro T hT hnot
    have hz : coeff T = 0 := by
      by_contra hnz
      exact hnot (Finset.mem_filter.mpr ⟨hT, hnz⟩)
    rw [hz, zero_mul]
  rw [hreindex]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc T (Finset.mem_filter.mp hT).1) (abs_nonneg _)

theorem weighted_global_coefficient_bounds {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) :
    (∑ T ∈ (B.biUnion blocks).powerset,
      lowerCoefficient B blocks orders T * BonferroniBlocks.intersectionMass C weight hit T) ≤
      (∑ x ∈ C, weight x * BonferroniBlocks.survives (B.biUnion blocks) (fun p => hit p x)) ∧
    (∑ x ∈ C, weight x * BonferroniBlocks.survives (B.biUnion blocks) (fun p => hit p x)) ≤
      ∑ T ∈ (B.biUnion blocks).powerset,
        upperCoefficient B blocks orders T * BonferroniBlocks.intersectionMass C weight hit T := by
  rw [weighted_coefficient_expansion, weighted_coefficient_expansion]
  simp_rw [lowerCoefficient_evaluation B blocks hdis, upperCoefficient_evaluation B blocks hdis]
  exact BonferroniBlocks.weighted_block_bounds C weight hweight B blocks orders hit

theorem layerCoefficient_density (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) :
    (∑ T ∈ P.powerset, layerCoefficient m T * ∏ p ∈ T, g p) =
      BonferroniDensity.elementarySum P g m := by
  classical
  unfold BonferroniDensity.elementarySum
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  unfold layerCoefficient
  split_ifs <;> simp

theorem correctionCoefficient_density (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j ∈ B) :
    (∑ T ∈ (B.biUnion blocks).powerset, correctionCoefficient B blocks orders j T * ∏ p ∈ T, g p) =
      BonferroniDensity.elementarySum (blocks j) g (2 * orders j + 1) *
        ∏ i ∈ B.erase j, BonferroniDensity.densityPolynomial (2 * orders i) (blocks i) g := by
  classical
  unfold correctionCoefficient
  rw [globalCoefficient_density B blocks hdis, ← Finset.mul_prod_erase B _ hj]
  simp only [ite_true, if_true]
  rw [layerCoefficient_density]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  simp only [ite_eq_right hij]
  rw [truncatedCoefficient_sum]
  rfl

theorem lowerCoefficient_density (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders : ℕ → ℕ) (g : ℕ → ℝ) :
    (∑ T ∈ (B.biUnion blocks).powerset, lowerCoefficient B blocks orders T * ∏ p ∈ T, g p) =
      (∏ j ∈ B, BonferroniDensity.densityPolynomial (2 * orders j) (blocks j) g) -
        ∑ j ∈ B, BonferroniDensity.elementarySum (blocks j) g (2 * orders j + 1) *
          ∏ i ∈ B.erase j, BonferroniDensity.densityPolynomial (2 * orders i) (blocks i) g := by
  unfold lowerCoefficient
  simp_rw [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_comm, upperCoefficient_density B blocks hdis]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact correctionCoefficient_density B blocks hdis orders g j hj

theorem upperCoefficient_card {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {T : Finset ℕ}
    (hc : upperCoefficient B blocks orders T ≠ 0) (j : ℕ) (hj : j ∈ B) :
    (T ∩ blocks j).card ≤ 2 * orders j := by
  exact (truncatedCoefficient_ne_zero_iff _ _).mp (Finset.prod_ne_zero_iff.mp hc j hj)

theorem lowerCoefficient_card {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {orders : ℕ → ℕ} {T : Finset ℕ}
    (hc : lowerCoefficient B blocks orders T ≠ 0) (j : ℕ) (hj : j ∈ B) :
    (T ∩ blocks j).card ≤ 2 * orders j + 1 := by
  classical
  by_cases hu : upperCoefficient B blocks orders T = 0
  · have hex : ∃ i ∈ B, correctionCoefficient B blocks orders i T ≠ 0 := by
      by_contra hnone
      have hsum : (∑ i ∈ B, correctionCoefficient B blocks orders i T) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_contra hiC
        exact hnone ⟨i, hi, hiC⟩
      apply hc
      rw [lowerCoefficient, hu, hsum, sub_self]
    obtain ⟨i, hi, hiC⟩ := hex
    by_cases hji : j = i
    · subst j
      exact le_of_eq (correctionCoefficient_own_card hi hiC)
    · exact (correctionCoefficient_other_card hj hji hiC).trans (Nat.le_succ _)
  · exact (upperCoefficient_card hu j hj).trans (Nat.le_succ _)

theorem prime_product_support (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (budget height : ℕ → ℕ) (hheight : ∀ j ∈ B, 1 ≤ height j)
    (hprime : ∀ j ∈ B, ∀ p ∈ blocks j, p.Prime)
    (hsize : ∀ j ∈ B, ∀ p ∈ blocks j, p ≤ height j)
    {T : Finset ℕ} (hT : T ⊆ B.biUnion blocks)
    (hcard : ∀ j ∈ B, (T ∩ blocks j).card ≤ budget j) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ ∏ j ∈ B, height j ^ budget j := by
  constructor
  · apply IntervalBoundingSieve.squarefree_primeSet_product
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp (hT hp)
    exact hprime j hj p hpj
  · have hprod : (∏ p ∈ T, p) = ∏ j ∈ B, ∏ p ∈ T ∩ blocks j, p := by
      simpa only [id_eq] using prod_inter_blocks B blocks hdis hT id
    rw [hprod]
    apply Finset.prod_le_prod'
    intro j hj
    exact (BonferroniBlocks.coefficient_divisor_support (blocks j) (hheight j hj)
      (hprime j hj) (hsize j hj) (hcard j hj)
      (Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, rfl⟩)).2

theorem lowerCoefficient_prime_support (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (orders height : ℕ → ℕ) (hheight : ∀ j ∈ B, 1 ≤ height j)
    (hprime : ∀ j ∈ B, ∀ p ∈ blocks j, p.Prime)
    (hsize : ∀ j ∈ B, ∀ p ∈ blocks j, p ≤ height j)
    {T : Finset ℕ} (hT : T ⊆ B.biUnion blocks) (hc : lowerCoefficient B blocks orders T ≠ 0) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ ∏ j ∈ B, height j ^ (2 * orders j + 1) :=
  prime_product_support B blocks hdis (fun j => 2 * orders j + 1) height hheight hprime hsize hT
    (lowerCoefficient_card hc)

theorem prime_product_injective (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (Q.powerset : Set (Finset ℕ)) := by
  intro T hT U hU heq
  have hTprod : (∏ p ∈ T, p).primeFactors = T :=
    Nat.primeFactors_prod (fun p hp => hprime p (Finset.mem_powerset.mp hT hp))
  have hUprod : (∏ p ∈ U, p).primeFactors = U :=
    Nat.primeFactors_prod (fun p hp => hprime p (Finset.mem_powerset.mp hU hp))
  change (∏ p ∈ T, p) = (∏ p ∈ U, p) at heq
  rw [← hTprod, ← hUprod, heq]

end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SquarefreeHarmonic
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped BigOperators ArithmeticFunction.Moebius

theorem sum_multiples_reverse (P l : ℕ) (hP : 0 < P) (hl : l ∣ P)
    (G : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then G (P / d) else 0) =
      ∑ t ∈ (P / l).divisors, G t := by
  have hPn : P ≠ 0 := ne_of_gt hP
  have hdvd : P / l ∣ P := Nat.div_dvd_of_dvd hl
  rw [← Nat.divisors_filter_dvd_of_dvd hPn hdvd, Finset.sum_filter]
  rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then G (P / d) else 0)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdP : d ∣ P := Nat.dvd_of_mem_divisors hd
  rw [Nat.div_div_self hdP hPn]
  have heq : l ∣ P / d ↔ d ∣ P / l := by
    rw [Nat.dvd_div_iff_mul_dvd hdP, Nat.dvd_div_iff_mul_dvd hl, Nat.mul_comm]
  simp only [heq]

theorem sum_lowerMobius (F : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ t ∈ m.divisors, lowerMobius F t) = F m := by
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr ?_) m hm
  intro n _
  rfl

theorem sum_inverseMultiples (P l : ℕ) (hP : 0 < P) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then inverseMultiples P y d else 0) = y l := by
  rw [show (∑ d ∈ P.divisors, if l ∣ d then inverseMultiples P y d else 0) =
      ∑ t ∈ (P / l).divisors, lowerMobius (fun t => y (P / t)) t by
    exact sum_multiples_reverse P l hP hl _]
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hl hP
  rw [sum_lowerMobius _ (Nat.div_pos (Nat.le_of_dvd hP hl) hlpos)]
  exact congrArg y (Nat.div_div_self hl (ne_of_gt hP))

theorem normalization_pos (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    0 < normalization s R := by
  have h1 : 1 ∈ s.prodPrimes.divisors := Nat.mem_divisors.mpr
    ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩
  have hone : s.selbergTerms 1 = 1 := s.selbergTerms_isMultiplicative.1
  have hnonneg : ∀ l ∈ s.prodPrimes.divisors,
      (0 : ℝ) ≤ if l ≤ R then s.selbergTerms l else 0 := by
    intro l hl
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).le
    · exact le_rfl
  have hle : (1 : ℝ) ≤ normalization s R := by
    simpa only [hR, ite_true, if_true, hone, normalization] using Finset.single_le_sum hnonneg h1
  exact lt_of_lt_of_le zero_lt_one hle

theorem nu_mul_optimizedWeight (s : BoundingSieve) (R : ℕ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    s.nu d * optimizedWeight s R d =
      inverseMultiples s.prodPrimes (diagonalTarget s R) d := by
  unfold optimizedWeight
  exact mul_div_cancel₀ _ (s.nu_ne_zero hd)

theorem optimized_diagonal_coordinates (s : BoundingSieve) (R : ℕ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimizedWeight s R d else 0) = diagonalTarget s R l := by
  have hrewrite : (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimizedWeight s R d else 0) =
      ∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then inverseMultiples s.prodPrimes (diagonalTarget s R) d else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [nu_mul_optimizedWeight s R (Nat.dvd_of_mem_divisors hd)]
  rw [hrewrite]
  exact sum_inverseMultiples s.prodPrimes l
    (Nat.pos_of_ne_zero s.prodPrimes_squarefree.ne_zero) hl _

theorem inverseMultiples_one (P : ℕ) (hP : 0 < P) (y : ℕ → ℝ) :
    inverseMultiples P y 1 = ∑ l ∈ P.divisors, (μ l : ℝ) * y l := by
  unfold inverseMultiples lowerMobius
  rw [Nat.div_one, Nat.sum_divisorsAntidiagonal (fun d e => (μ d : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hl) (ne_of_gt hP)]

theorem optimizedWeight_one (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    optimizedWeight s R 1 = 1 := by
  have hP : 0 < s.prodPrimes := Nat.pos_of_ne_zero s.prodPrimes_squarefree.ne_zero
  have hH : normalization s R ≠ 0 := ne_of_gt (normalization_pos s hR)
  have hn1 : s.nu 1 = 1 := s.nu_mult.1
  unfold optimizedWeight
  rw [hn1, div_one, inverseMultiples_one _ hP]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (μ l : ℝ) * diagonalTarget s R l =
        (if l ≤ R then s.selbergTerms l else 0) / normalization s R := by
    intro l hl
    have hsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl))
    unfold diagonalTarget
    split_ifs
    · calc
        (μ l : ℝ) * ((μ l : ℝ) * s.selbergTerms l / normalization s R) =
            (μ l : ℝ) ^ 2 * s.selbergTerms l / normalization s R := by ring
        _ = _ := by rw [hsq, one_mul]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  exact div_self hH

theorem optimized_upperMoebius (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared (optimizedWeight s R)) :=
  BoundingSieve.upperMoebius_lambdaSquared _ (optimizedWeight_one s hR)

theorem optimized_mainSum (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    s.mainSum (BoundingSieve.lambdaSquared (optimizedWeight s R)) =
      (normalization s R)⁻¹ := by
  have hH : normalization s R ≠ 0 := ne_of_gt (normalization_pos s hR)
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then s.nu d * optimizedWeight s R d else 0) ^ 2 =
      (if l ≤ R then s.selbergTerms l else 0) / (normalization s R) ^ 2 := by
    intro l hl
    have hldiv := Nat.dvd_of_mem_divisors hl
    have hg : s.selbergTerms l ≠ 0 := ne_of_gt (s.selbergTerms_pos hldiv)
    have hsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.prodPrimes_squarefree.squarefree_of_dvd hldiv)
    rw [optimized_diagonal_coordinates s R hldiv]
    unfold diagonalTarget
    split_ifs
    · rw [div_pow, mul_pow, hsq, one_mul]
      field_simp
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  change normalization s R / (normalization s R) ^ 2 = _
  field_simp

theorem lowerMobius_abs_le (F : ℕ → ℝ) (m : ℕ) :
    |lowerMobius F m| ≤ ∑ t ∈ m.divisors, |F t| := by
  unfold lowerMobius
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (μ d : ℝ) * F e)]
  calc
    |∑ d ∈ m.divisors, (μ d : ℝ) * F (m / d)| ≤
        ∑ d ∈ m.divisors, |(μ d : ℝ) * F (m / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ m.divisors, |F (m / d)| := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul]
      have hmu : |(μ d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (abs_nonneg (F (m / d)))
    _ = _ := Nat.sum_div_divisors m (fun d => |F d|)

theorem sum_abs_diagonalTarget (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    (∑ l ∈ s.prodPrimes.divisors, |diagonalTarget s R l|) = 1 := by
  have hH : 0 < normalization s R := normalization_pos s hR
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      |diagonalTarget s R l| =
        (if l ≤ R then s.selbergTerms l else 0) / normalization s R := by
    intro l hl
    have hg := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    have hmu : |(μ l : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl))
    unfold diagonalTarget
    split_ifs
    · rw [abs_div, abs_mul, hmu, one_mul, abs_of_pos hg, abs_of_pos hH]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  exact div_self (ne_of_gt hH)

theorem optimizedWeight_abs_le_inv_nu (s : BoundingSieve) {R d : ℕ}
    (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    |optimizedWeight s R d| ≤ (s.nu d)⁻¹ := by
  have hnu : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hd
  have hmass : |inverseMultiples s.prodPrimes (diagonalTarget s R) d| ≤ 1 := by
    unfold inverseMultiples
    calc
      _ ≤ ∑ t ∈ (s.prodPrimes / d).divisors,
          |diagonalTarget s R (s.prodPrimes / t)| := lowerMobius_abs_le _ _
      _ ≤ ∑ t ∈ s.prodPrimes.divisors, |diagonalTarget s R (s.prodPrimes / t)| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Nat.divisors_subset_of_dvd s.prodPrimes_squarefree.ne_zero (Nat.div_dvd_of_dvd hd))
        intro i _ _
        exact abs_nonneg _
      _ = ∑ l ∈ s.prodPrimes.divisors, |diagonalTarget s R l| :=
        Nat.sum_div_divisors s.prodPrimes (fun l => |diagonalTarget s R l|)
      _ = 1 := sum_abs_diagonalTarget s hR
  unfold optimizedWeight
  rw [abs_div, abs_of_pos hnu, inv_eq_one_div]
  exact div_le_div_of_nonneg_right hmass hnu.le

theorem optimizedWeight_eq_zero_of_cutoff_lt (s : BoundingSieve) {R d : ℕ}
    (hd : d ∣ s.prodPrimes) (hRd : R < d) : optimizedWeight s R d = 0 := by
  unfold optimizedWeight inverseMultiples lowerMobius
  suffices (∑ t ∈ (s.prodPrimes / d).divisorsAntidiagonal,
      (μ t.1 : ℝ) * diagonalTarget s R (s.prodPrimes / t.2)) = 0 by
    rw [this, zero_div]
  apply Finset.sum_eq_zero
  intro t ht
  have htdiv : t.2 ∣ s.prodPrimes / d :=
    Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal ht)
  have htP : t.2 ∣ s.prodPrimes := htdiv.trans (Nat.div_dvd_of_dvd hd)
  have hdq : d ∣ s.prodPrimes / t.2 := by
    rw [Nat.dvd_div_iff_mul_dvd htP, Nat.mul_comm]
    exact (Nat.dvd_div_iff_mul_dvd hd).mp htdiv
  have hqpos : 0 < s.prodPrimes / t.2 := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_squarefree.ne_zero) htP)
    (Nat.pos_of_dvd_of_pos htP (Nat.pos_of_ne_zero s.prodPrimes_squarefree.ne_zero))
  have hRq : R < s.prodPrimes / t.2 := hRd.trans_le (Nat.le_of_dvd hqpos hdq)
  simp only [diagonalTarget, ite_eq_right (not_le_of_gt hRq), mul_zero]

theorem sum_lambdaSquared (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d) =
      (∑ d ∈ P.divisors, w d) ^ 2 := by
  unfold BoundingSieve.lambdaSquared
  have henlarge :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then w a * w b else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then w a * w b else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    suffices ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = a.lcm b) = (d = a.lcm b) by
      simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, Finset.sum_filter,
        Finset.ite_sum_zero, ← ite_and, this]
    simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
  rw [henlarge, Finset.sum_comm]
  calc
    _ = ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, w a * w b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      have hlcm : a.lcm b ∈ P.divisors := Nat.mem_divisors.mpr
        ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb),
          (Nat.mem_divisors.mp ha).2⟩
      rw [Finset.sum_ite_eq_of_mem' P.divisors (a.lcm b) _ hlcm]
    _ = _ := by rw [sq, Finset.sum_mul]; simp only [Finset.mul_sum]

theorem sum_abs_lambdaSquared_le (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  have hterm : ∀ d, |BoundingSieve.lambdaSquared w d| ≤
      BoundingSieve.lambdaSquared (fun a => |w a|) d := by
    intro d
    unfold BoundingSieve.lambdaSquared
    calc
      _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
          if d = a.lcm b then w a * w b else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
          |if d = a.lcm b then w a * w b else 0| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_ite, abs_mul, abs_zero]
  calc
    _ ≤ ∑ d ∈ P.divisors, BoundingSieve.lambdaSquared (fun a => |w a|) d :=
      Finset.sum_le_sum fun d _ => hterm d
    _ = _ := sum_lambdaSquared _ _

theorem optimizedWeight_sum_abs_le_sq (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R)
    (hnu : ∀ d, d ∣ s.prodPrimes → s.nu d = (d : ℝ)⁻¹) :
    (∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d|) ≤ (R : ℝ) ^ 2 := by
  classical
  let D := s.prodPrimes.divisors.filter fun d => d ≤ R
  have hrestricted : (∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d|) =
      ∑ d ∈ D, |optimizedWeight s R d| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hRd : R < d := by
      have : ¬ d ≤ R := fun hdR => hnot (Finset.mem_filter.mpr ⟨hd, hdR⟩)
      omega
    rw [optimizedWeight_eq_zero_of_cutoff_lt s (Nat.dvd_of_mem_divisors hd) hRd, abs_zero]
  have hDsub : D ⊆ Finset.Icc 1 R := by
    intro d hd
    obtain ⟨hdP, hdR⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdR⟩
  have hDcard : D.card ≤ R := by
    simpa using Finset.card_le_card hDsub
  rw [hrestricted]
  calc
    _ ≤ ∑ _d ∈ D, (R : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdP, hdR⟩ := Finset.mem_filter.mp hd
      have hpoint := optimizedWeight_abs_le_inv_nu s hR (Nat.dvd_of_mem_divisors hdP)
      rw [hnu d (Nat.dvd_of_mem_divisors hdP), inv_inv] at hpoint
      exact hpoint.trans (by exact_mod_cast hdR)
    _ = (D.card : ℝ) * R := by simp
    _ ≤ (R : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hDcard) (Nat.cast_nonneg R)

theorem optimized_lambda_error_norm (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R)
    (hnu : ∀ d, d ∣ s.prodPrimes → s.nu d = (d : ℝ)⁻¹) :
    (∑ d ∈ s.prodPrimes.divisors,
      |BoundingSieve.lambdaSquared (optimizedWeight s R) d|) ≤ (R : ℝ) ^ 4 := by
  have hsum := optimizedWeight_sum_abs_le_sq s hR hnu
  have hnonneg : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d|) ^ 2 :=
      sum_abs_lambdaSquared_le _ _
    _ ≤ (R : ℝ) ^ 4 := by nlinarith [sq_nonneg ((R : ℝ)^2 -
      ∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d|)]

theorem cutoffNormalization_pos (z : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    0 < cutoffNormalization z R := normalization_pos _ hR

theorem cutoffSurvivors_le_optimized (J z : ℕ) (residue : ℕ → ℕ)
    {R : ℕ} (hR : 1 ≤ R) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      (J : ℝ) / cutoffNormalization z R + (R : ℝ) ^ 4 := by
  let s := IntervalBoundingSieve.intervalSieve 0 0
    (IntervalBoundingSieve.cutoffProduct z) (IntervalBoundingSieve.cutoffProduct_squarefree z)
  let muPlus := BoundingSieve.lambdaSquared (optimizedWeight s R)
  have hmu : BoundingSieve.IsUpperMoebius muPlus := optimized_upperMoebius s hR
  have hs := IntervalBoundingSieve.cutoffSurvivors_card_le_upperMoebius J z residue muPlus hmu
  have hmain : (∑ d ∈ (IntervalBoundingSieve.cutoffProduct z).divisors, muPlus d / d) =
      (cutoffNormalization z R)⁻¹ := by
    change (∑ d ∈ s.prodPrimes.divisors, muPlus d / d) = (normalization s R)⁻¹
    have heq : (∑ d ∈ s.prodPrimes.divisors, muPlus d / d) = s.mainSum muPlus := by
      rfl
    rw [heq]
    exact optimized_mainSum s hR
  have herr : (∑ d ∈ (IntervalBoundingSieve.cutoffProduct z).divisors, |muPlus d|) ≤
      (R : ℝ) ^ 4 := by
    apply optimized_lambda_error_norm s hR
    intro d _
    rfl
  rw [hmain, ← div_eq_mul_inv] at hs
  exact hs.trans (add_le_add le_rfl herr)

end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped BigOperators

theorem interval_subset_square_product (R : ℕ) :
    Finset.Icc 1 R ⊆
      ((squarefreeUpTo R).product (Finset.Icc 1 R)).image
        (fun t : ℕ × ℕ => t.2 ^ 2 * t.1) := by
  classical
  intro n hn
  obtain ⟨hnpos, hnR⟩ := Finset.mem_Icc.mp hn
  obtain ⟨d, a, hd, ha, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos hnpos
  have hdle : d ≤ n := Nat.le_of_dvd hnpos ⟨a ^ 2, by nlinarith [heq]⟩
  have hale : a ≤ n := by
    have ha2 : a ≤ a ^ 2 := by nlinarith
    have hmul : a ^ 2 ≤ a ^ 2 * d := Nat.le_mul_of_pos_right _ hd
    exact ha2.trans (hmul.trans_eq heq)
  exact Finset.mem_image.mpr ⟨(d, a), Finset.mem_product.mpr
    ⟨mem_squarefreeUpTo.mpr ⟨hd, hdle.trans hnR, hsf⟩,
      Finset.mem_Icc.mpr ⟨ha, hale.trans hnR⟩⟩, heq⟩

theorem sum_inv_sq_le_two (R : ℕ) :
    (∑ a ∈ Finset.Icc 1 R, ((a : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hset : Finset.Ioo 0 (R + 1) = Finset.Icc 1 R := by
    ext a
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  simpa only [hset, Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (R + 1))

theorem harmonic_le_twice_squarefreeHarmonic (R : ℕ) :
    (harmonic R : ℝ) ≤ 2 * squarefreeHarmonic R := by
  classical
  let T := (squarefreeUpTo R).product (Finset.Icc 1 R)
  let f : ℕ × ℕ → ℕ := fun t => t.2 ^ 2 * t.1
  have hnonneg : 0 ≤ squarefreeHarmonic R := Finset.sum_nonneg fun _ _ => by positivity
  calc
    (harmonic R : ℝ) = ∑ n ∈ Finset.Icc 1 R, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ ∑ n ∈ T.image f, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (interval_subset_square_product R)
      intro n _ _
      positivity
    _ ≤ ∑ t ∈ T, ((f t : ℕ) : ℝ)⁻¹ :=
      Finset.sum_image_le_of_nonneg (fun n _ => by positivity)
    _ = squarefreeHarmonic R * ∑ a ∈ Finset.Icc 1 R, ((a : ℝ) ^ 2)⁻¹ := by
      simp only [T, f, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, squarefreeHarmonic]
      rw [Finset.product_eq_sprod, Finset.sum_product' (squarefreeUpTo R) (Finset.Icc 1 R)
        (fun d a => (d : ℝ)⁻¹ * ((a : ℝ)^2)⁻¹), Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ squarefreeHarmonic R * 2 :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_le_two R) hnonneg
    _ = _ := mul_comm _ _

theorem log_le_twice_squarefreeHarmonic (R : ℕ) :
    Real.log (R + 1) ≤ 2 * squarefreeHarmonic R := by
  have hlog : Real.log ((R + 1 : ℕ) : ℝ) ≤ harmonic R := log_add_one_le_harmonic R
  push_cast at hlog
  exact hlog.trans (harmonic_le_twice_squarefreeHarmonic R)

theorem nu_le_selbergTerms (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) : s.nu d ≤ s.selbergTerms d := by
  rw [s.selbergTerms_apply]
  have hprod : (1 : ℝ) ≤ ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
    apply Finset.one_le_prod
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
    have hp0 := s.nu_pos_of_prime p hpprime hpP
    have hp1 := s.nu_lt_one_of_prime p hpprime hpP
    exact (one_le_inv₀ (by linarith)).mpr (by linarith)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hprod (s.nu_pos_of_dvd_prodPrimes hd).le

theorem squarefreeUpTo_subset_cutoff_divisors {R z : ℕ} (hRz : R ≤ z) :
    squarefreeUpTo R ⊆ (IntervalBoundingSieve.cutoffProduct z).divisors.filter
      (fun d => d ≤ R) := by
  classical
  intro d hd
  obtain ⟨hd0, hdR, hsf⟩ := mem_squarefreeUpTo.mp hd
  have hprimeSub : d.primeFactors ⊆ LargePrimeDeletion.cutoffPrimes z := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact LargePrimeDeletion.mem_cutoffPrimes.mpr
      ⟨hpp, (Nat.le_of_dvd hd0 hpd).trans (hdR.trans hRz)⟩
  have hdiv : d ∣ IntervalBoundingSieve.cutoffProduct z := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_dvd_prod_of_subset _ _ id hprimeSub
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hdiv, (IntervalBoundingSieve.cutoffProduct_squarefree z).ne_zero⟩,
      hdR⟩

theorem squarefreeHarmonic_le_selberg_sum {R z : ℕ} (hRz : R ≤ z) :
    squarefreeHarmonic R ≤
      ∑ d ∈ (IntervalBoundingSieve.cutoffProduct z).divisors,
        if d ≤ R then
          (IntervalBoundingSieve.intervalSieve 0 0 (IntervalBoundingSieve.cutoffProduct z)
            (IntervalBoundingSieve.cutoffProduct_squarefree z)).selbergTerms d else 0 := by
  classical
  let s := IntervalBoundingSieve.intervalSieve 0 0 (IntervalBoundingSieve.cutoffProduct z)
    (IntervalBoundingSieve.cutoffProduct_squarefree z)
  let D := s.prodPrimes.divisors.filter fun d => d ≤ R
  have hsub : squarefreeUpTo R ⊆ D := squarefreeUpTo_subset_cutoff_divisors hRz
  change squarefreeHarmonic R ≤ ∑ d ∈ s.prodPrimes.divisors,
    if d ≤ R then s.selbergTerms d else 0
  calc
    squarefreeHarmonic R = ∑ d ∈ squarefreeUpTo R, s.nu d := rfl
    _ ≤ ∑ d ∈ squarefreeUpTo R, s.selbergTerms d := by
      apply Finset.sum_le_sum
      intro d hd
      exact nu_le_selbergTerms s (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp (hsub hd)).1)
    _ ≤ ∑ d ∈ D, s.selbergTerms d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d hd _
      exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le
    _ = _ := Finset.sum_filter _ _

theorem log_le_twice_selberg_sum {R z : ℕ} (hRz : R ≤ z) :
    Real.log (R + 1) ≤
      2 * ∑ d ∈ (IntervalBoundingSieve.cutoffProduct z).divisors,
        if d ≤ R then
          (IntervalBoundingSieve.intervalSieve 0 0 (IntervalBoundingSieve.cutoffProduct z)
            (IntervalBoundingSieve.cutoffProduct_squarefree z)).selbergTerms d else 0 := by
  exact (log_le_twice_squarefreeHarmonic R).trans
    (mul_le_mul_of_nonneg_left (squarefreeHarmonic_le_selberg_sum hRz) (by norm_num))

theorem log_le_twice_cutoffNormalization {R z : ℕ} (hRz : R ≤ z) :
    Real.log (R + 1) ≤ 2 * SelbergOptimization.cutoffNormalization z R :=
  log_le_twice_selberg_sum hRz

theorem cutoffSurvivors_le_log_bound (J z : ℕ) (residue : ℕ → ℕ)
    {R : ℕ} (hR : 1 ≤ R) (hRz : R ≤ z) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      2 * (J : ℝ) / Real.log (R + 1) + (R : ℝ) ^ 4 := by
  have hH : 0 < SelbergOptimization.cutoffNormalization z R :=
    SelbergOptimization.cutoffNormalization_pos z hR
  have hlog : 0 < Real.log (R + 1) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hR)
  have hlower := log_le_twice_cutoffNormalization hRz
  have hdiv : (J : ℝ) / SelbergOptimization.cutoffNormalization z R ≤
      2 * (J : ℝ) / Real.log (R + 1) := by
    apply (div_le_div_iff₀ hH hlog).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg J) (sub_nonneg.mpr hlower)]
  exact (SelbergOptimization.cutoffSurvivors_le_optimized J z residue hR).trans
    (add_le_add hdiv le_rfl)

theorem cutoffSurvivors_le_seventeen_of_eighth_radius
    (J z : ℕ) (residue : ℕ → ℕ) {R : ℕ}
    (hR : 2 ≤ R) (hRz : R ≤ z) (hlo : R ^ 8 ≤ J) (hhi : J ≤ (R + 1) ^ 8) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      17 * (J : ℝ) / Real.log J := by
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hJlo : (R : ℝ) ^ 8 ≤ J := by exact_mod_cast hlo
  have hJhi : (J : ℝ) ≤ ((R : ℝ) + 1) ^ 8 := by exact_mod_cast hhi
  have hR8 : (256 : ℝ) ≤ (R : ℝ) ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hRreal 8
    norm_num at this
    exact this
  have hJone : (1 : ℝ) < J := by linarith
  have hJpos : (0 : ℝ) < J := by linarith
  have hlogJpos : 0 < Real.log (J : ℝ) := Real.log_pos hJone
  have hlogRpos : 0 < Real.log ((R : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogupper : Real.log (J : ℝ) ≤ 8 * Real.log ((R : ℝ) + 1) := by
    have h := Real.log_le_log hJpos hJhi
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hlogRle : Real.log ((R : ℝ) + 1) ≤ R := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (R : ℝ) + 1 by positivity)
    linarith
  have hcube : (8 : ℝ) ≤ (R : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hRreal 3
    norm_num at this
    exact this
  have height : (8 : ℝ) * R ≤ (R : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hcube (Nat.cast_nonneg R)
    nlinarith
  have hlogJle : Real.log (J : ℝ) ≤ (R : ℝ) ^ 4 := by linarith
  have hmain : 2 * (J : ℝ) / Real.log ((R : ℝ) + 1) ≤
      16 * (J : ℝ) / Real.log (J : ℝ) := by
    apply (div_le_div_iff₀ hlogRpos hlogJpos).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg J) (sub_nonneg.mpr hlogupper)]
  have herr : (R : ℝ) ^ 4 ≤ (J : ℝ) / Real.log (J : ℝ) := by
    apply (le_div_iff₀ hlogJpos).mpr
    calc
      (R : ℝ) ^ 4 * Real.log (J : ℝ) ≤ (R : ℝ) ^ 4 * (R : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hlogJle (pow_nonneg (Nat.cast_nonneg R) _)
      _ = (R : ℝ) ^ 8 := by ring
      _ ≤ _ := hJlo
  calc
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
        2 * (J : ℝ) / Real.log ((R : ℝ) + 1) + (R : ℝ) ^ 4 :=
      cutoffSurvivors_le_log_bound J z residue (by omega) hRz
    _ ≤ 16 * (J : ℝ) / Real.log (J : ℝ) + (J : ℝ) / Real.log (J : ℝ) :=
      add_le_add hmain herr
    _ = _ := by ring

theorem cutoffSurvivors_le_seventeen (J z : ℕ) (residue : ℕ → ℕ)
    (hJ : 256 ≤ J) (hz : Nat.nthRoot 8 J ≤ z) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      17 * (J : ℝ) / Real.log J := by
  apply cutoffSurvivors_le_seventeen_of_eighth_radius J z residue (R := Nat.nthRoot 8 J)
  · apply (Nat.le_nthRoot_iff (by norm_num : 8 ≠ 0)).mpr
    norm_num
    exact hJ
  · exact hz
  · exact Nat.pow_nthRoot_le (Or.inl (by norm_num : 8 ≠ 0))
  · exact (Nat.lt_pow_nthRoot_add_one (by norm_num : 8 ≠ 0) J).le

theorem cutoffSurvivors_le_seventeen_of_le_cutoff (J z : ℕ) (residue : ℕ → ℕ)
    (hJ : 256 ≤ J) (hJz : J ≤ z) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      17 * (J : ℝ) / Real.log J := by
  apply cutoffSurvivors_le_seventeen J z residue hJ
  exact ((Nat.le_self_pow (by norm_num : 8 ≠ 0) (Nat.nthRoot 8 J)).trans
    (Nat.pow_nthRoot_le (Or.inl (by norm_num : 8 ≠ 0)))).trans hJz

theorem cutoffSurvivors_le_uniform_log (J z : ℕ) (residue : ℕ → ℕ) (hJz : J ≤ z) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤
      255 * (1 + (J : ℝ) / Real.log J) := by
  have hquot : 0 ≤ (J : ℝ) / Real.log J := by
    by_cases hJ0 : J = 0
    · simp [hJ0]
    · apply div_nonneg (Nat.cast_nonneg J)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hJ0
  by_cases hJ : 256 ≤ J
  · have hbound := cutoffSurvivors_le_seventeen_of_le_cutoff J z residue hJ hJz
    calc
      _ ≤ 17 * (J : ℝ) / Real.log J := hbound
      _ ≤ _ := by rw [mul_div_assoc]; nlinarith
  · have hsmall : J ≤ 255 := by omega
    have hsubset : LargePrimeDeletion.cutoffSurvivors J z residue ⊆ Finset.range J := by
      intro i hi
      exact Finset.mem_range.mpr (LargePrimeDeletion.mem_cutoffSurvivors.mp hi).1
    have hcount : (LargePrimeDeletion.cutoffSurvivors J z residue).card ≤ J := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    have hcountR : ((LargePrimeDeletion.cutoffSurvivors J z residue).card : ℝ) ≤ 255 := by
      exact_mod_cast hcount.trans hsmall
    nlinarith

end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeDensityBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped BigOperators

theorem dyadicPrimes_subset_survivors (n : ℕ) :
    dyadicPrimes n ⊆ {n} ∪
      (LargePrimeDeletion.cutoffSurvivors n n (LargePrimeDeletion.divisibilityResidue (n : ℤ))).image
        (fun i => n + i) := by
  intro p hp
  obtain ⟨hnp, hp2n, hprime⟩ := mem_dyadicPrimes.mp hp
  by_cases heq : p = n
  · exact Finset.mem_union_left _ (by simp [heq])
  · have hnp' : n < p := lt_of_le_of_ne hnp (Ne.symm heq)
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨p - n, ?_, Nat.add_sub_of_le hnp⟩
    apply LargePrimeDeletion.mem_cutoffSurvivors.mpr
    refine ⟨by omega, ?_⟩
    intro q hq hqn hbad
    have hdiv := (LargePrimeDeletion.divisibility_iff_modEq (n : ℤ) hq.pos (p - n)).mpr hbad
    have hdivN : q ∣ p := by
      have hnEq : (n : ℤ) + (p - n : ℕ) = p := by exact_mod_cast Nat.add_sub_of_le hnp
      rw [hnEq] at hdiv
      exact Int.natCast_dvd_natCast.mp hdiv
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hprime).mp hdivN
    omega

theorem dyadicPrimes_card_le (n : ℕ) :
    ((dyadicPrimes n).card : ℝ) ≤ 1 + 255 * (1 + (n : ℝ) / Real.log n) := by
  let C := LargePrimeDeletion.cutoffSurvivors n n (LargePrimeDeletion.divisibilityResidue (n : ℤ))
  have hcard : (dyadicPrimes n).card ≤ 1 + C.card := by
    calc
      _ ≤ ({n} ∪ C.image (fun i => n + i)).card := Finset.card_le_card (dyadicPrimes_subset_survivors n)
      _ ≤ ({n} : Finset ℕ).card + (C.image (fun i => n + i)).card := Finset.card_union_le _ _
      _ ≤ 1 + C.card := by simpa using Nat.add_le_add_left (Finset.card_image_le) 1
  have hcardR : ((dyadicPrimes n).card : ℝ) ≤ 1 + (C.card : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (add_le_add le_rfl
    (SquarefreeHarmonic.cutoffSurvivors_le_uniform_log n n _ le_rfl))

theorem self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ]
      omega

theorem dyadic_density_sum_le (k : ℕ) (hk : 1 ≤ k) (g : ℕ → ℝ)
    (hg : ∀ p ∈ dyadicPrimes (2 ^ k), g p ≤ 2 / p) :
    (∑ p ∈ dyadicPrimes (2 ^ k), g p) ≤ 1532 / (k : ℝ) := by
  let n : ℕ := 2 ^ k
  have hnpos : (0 : ℝ) < n := by dsimp [n] <;> positivity
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast self_le_two_pow k
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogeq : Real.log (n : ℝ) = (k : ℝ) * Real.log 2 := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hloglower : (k : ℝ) / 2 ≤ Real.log (n : ℝ) := by
    rw [hlogeq]
    nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hlog2)]
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hsum : (∑ p ∈ dyadicPrimes n, g p) ≤ ((dyadicPrimes n).card : ℝ) * (2 / n) := by
    calc
      _ ≤ ∑ _p ∈ dyadicPrimes n, (2 / n : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        apply (hg p hp).trans
        exact div_le_div_of_nonneg_left (by norm_num) hnpos
          (by exact_mod_cast (mem_dyadicPrimes.mp hp).1)
      _ = _ := by simp
  have hcount := dyadicPrimes_card_le n
  have hfirst : (512 : ℝ) / n ≤ 512 / (k : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hkpos hkn
  have hsecond : (510 : ℝ) / Real.log (n : ℝ) ≤ 1020 / (k : ℝ) := by
    apply (div_le_div_iff₀ hlogpos hkpos).mpr
    nlinarith
  calc
    (∑ p ∈ dyadicPrimes (2 ^ k), g p) ≤ ((dyadicPrimes n).card : ℝ) * (2 / n) := hsum
    _ ≤ (1 + 255 * (1 + (n : ℝ) / Real.log n)) * (2 / n) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (512 : ℝ) / n + 510 / Real.log (n : ℝ) := by field_simp <;> ring
    _ ≤ 512 / (k : ℝ) + 1020 / (k : ℝ) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem dyadicPrimes_disjoint {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dyadicPrimes (2 ^ k)) (dyadicPrimes (2 ^ l)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hk
  obtain ⟨hkp, hpk, _⟩ := mem_dyadicPrimes.mp hp
  obtain ⟨hlp, hpl, _⟩ := mem_dyadicPrimes.mp hk
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · have hpow : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hlt)
    rw [pow_succ, Nat.mul_comm] at hpow
    omega
  · have hpow : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hlt)
    rw [pow_succ, Nat.mul_comm] at hpow
    omega

theorem geometricPrimes_eq_dyadic_union (j : ℕ) :
    geometricPrimes j = (Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1))).biUnion
      (fun k => dyadicPrimes (2 ^ k)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hlo, hhi, hprime⟩ := mem_geometricPrimes.mp hp
    let k := Nat.log 2 p
    have hklo : 2 ^ j ≤ k := Nat.le_log_of_pow_le (by norm_num) hlo
    have hkhi : k < 2 ^ (j + 1) := Nat.log_lt_of_lt_pow hprime.ne_zero hhi
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_Ico.mpr ⟨hklo, hkhi⟩, ?_⟩
    apply mem_dyadicPrimes.mpr
    refine ⟨Nat.pow_log_le_self 2 hprime.ne_zero, ?_, hprime⟩
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
    simpa only [pow_succ, Nat.mul_comm] using h
  · intro hp
    obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hklo, hkhi⟩ := Finset.mem_Ico.mp hk
    obtain ⟨hkp, hpk, hprime⟩ := mem_dyadicPrimes.mp hpk
    apply mem_geometricPrimes.mpr
    refine ⟨(Nat.pow_le_pow_right (by norm_num) hklo).trans hkp, ?_, hprime⟩
    have hpow : 2 ^ (k + 1) ≤ 2 ^ (2 ^ (j + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hkhi)
    rw [pow_succ, Nat.mul_comm] at hpow
    exact hpk.trans_le hpow

theorem geometric_reciprocal_sum_le (j : ℕ) :
    (∑ p ∈ geometricPrimes j, (2 : ℝ) / p) ≤ 1532 := by
  rw [geometricPrimes_eq_dyadic_union]
  rw [Finset.sum_biUnion (fun k _ l _ hkl => dyadicPrimes_disjoint hkl)]
  have hKpos : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  calc
    _ ≤ ∑ k ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1)), (1532 : ℝ) / (k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := (Nat.one_le_pow _ _ (by norm_num)).trans (Finset.mem_Ico.mp hk).1
      exact dyadic_density_sum_le k hk1 (fun p => (2 : ℝ) / p) (fun _ _ => le_rfl)
    _ ≤ ∑ _k ∈ Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1)), (1532 : ℝ) / (2 ^ j : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact div_le_div_of_nonneg_left (by norm_num) hKpos
        (by exact_mod_cast (Finset.mem_Ico.mp hk).1)
    _ = 1532 := by
      have hcard : (Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1))).card = 2 ^ j := by
        rw [Nat.card_Ico, pow_succ]
        omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      field_simp

theorem subset_geometric_density_sum_le (j : ℕ) (Q : Finset ℕ) (hQ : Q ⊆ geometricPrimes j)
    (g : ℕ → ℝ) (hg : ∀ p ∈ Q, g p ≤ 2 / p) : (∑ p ∈ Q, g p) ≤ 1532 := by
  calc
    _ ≤ ∑ p ∈ Q, (2 : ℝ) / p := Finset.sum_le_sum hg
    _ ≤ ∑ p ∈ geometricPrimes j, (2 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
    _ ≤ _ := geometric_reciprocal_sum_le j

theorem geometricPrimes_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (geometricPrimes i) (geometricPrimes j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hil, hiu, _⟩ := mem_geometricPrimes.mp hp
  obtain ⟨hjl, hju, _⟩ := mem_geometricPrimes.mp hq
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hexp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hlt)
    have hpowers := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hexp
    omega
  · have hexp : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hlt)
    have hpowers := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hexp
    omega

theorem primeBlock_pairwise (V : ℕ) (P : Finset ℕ) :
    (blockIndices V : Set ℕ).Pairwise fun i j => Disjoint (primeBlock P i) (primeBlock P j) := by
  intro i _ j _ hij
  exact (geometricPrimes_disjoint hij).mono Finset.inter_subset_right Finset.inter_subset_right

theorem primeBlock_union (V : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hV : ∀ p ∈ P, p ≤ V) :
    (blockIndices V).biUnion (primeBlock P) = P := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpj).1
  · intro hp
    have hpp := hprime p hp
    let k := Nat.log 2 p
    let j := Nat.log 2 k
    have hk1 : 1 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by simpa using hpp.two_le)
    have hk0 : k ≠ 0 := by omega
    have hjlast : j ≤ lastBlock V := Nat.log_mono_right (Nat.log_mono_right (hV p hp))
    have hlo : 2 ^ (2 ^ j) ≤ p :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_log_le_self 2 hk0)).trans
        (Nat.pow_log_le_self 2 hpp.ne_zero)
    have hhi : p < 2 ^ (2 ^ (j + 1)) := by
      have hkj : k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      have hpk : p < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
      exact hpk.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hkj))
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjlast),
      Finset.mem_inter.mpr ⟨hp, mem_geometricPrimes.mpr ⟨hlo, hhi, hpp⟩⟩⟩

theorem primeBlock_density_sum_le (P : Finset ℕ) (j : ℕ) (g : ℕ → ℝ)
    (hdim : ∀ p ∈ P, g p ≤ 2 / p) : (∑ p ∈ primeBlock P j, g p) ≤ 1532 :=
  subset_geometric_density_sum_le j _ Finset.inter_subset_right g
    (fun p hp => hdim p (Finset.mem_inter.mp hp).1)

theorem supportCost_succ (m J : ℕ) :
    supportCost m (J + 1) = supportCost (m + 1) J + 2 ^ (J + 2) * (2 * m + 1) := by
  unfold supportCost
  rw [Finset.sum_range_succ]
  have hsum : (∑ j ∈ Finset.range (J + 1), 2 ^ (j + 1) * (2 * reverseOrder m (J + 1) j + 1)) =
      ∑ j ∈ Finset.range (J + 1), 2 ^ (j + 1) * (2 * reverseOrder (m + 1) J j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have horder : reverseOrder m (J + 1) j = reverseOrder (m + 1) J j := by
      unfold reverseOrder
      omega
    rw [horder]
  rw [hsum]
  simp only [reverseOrder, Nat.sub_self, Nat.add_zero]

theorem supportCost_le (m J : ℕ) : supportCost m J ≤ (8 * m + 12) * 2 ^ J := by
  induction J generalizing m with
  | zero => simp [supportCost, reverseOrder]; omega
  | succ J ih =>
      rw [supportCost_succ]
      calc
        _ ≤ (8 * (m + 1) + 12) * 2 ^ J + 2 ^ (J + 2) * (2 * m + 1) :=
          Nat.add_le_add_right (ih (m + 1)) _
        _ = (8 * m + 12) * 2 ^ (J + 1) := by simp only [pow_add] <;> norm_num <;> ring

theorem supportCost_le_twelve (m J : ℕ) : supportCost m J ≤ 12 * (m + 1) * 2 ^ J := by
  apply (supportCost_le m J).trans
  exact Nat.mul_le_mul_right (2 ^ J) (by omega)

theorem lastBlock_lower_le (V : ℕ) (hV : 2 ≤ V) : 2 ^ (2 ^ lastBlock V) ≤ V := by
  have hlog1 : 1 ≤ Nat.log 2 V := Nat.le_log_of_pow_le (by norm_num) (by simpa using hV)
  have hlog0 : Nat.log 2 V ≠ 0 := by omega
  have hinner : 2 ^ lastBlock V ≤ Nat.log 2 V := Nat.pow_log_le_self 2 hlog0
  exact (Nat.pow_le_pow_right (by norm_num) hinner).trans (Nat.pow_log_le_self 2 (by omega))

theorem supportHeight_product_le (V m : ℕ) (hV : 2 ≤ V) :
    (∏ j ∈ blockIndices V, (2 ^ (2 ^ (j + 1))) ^ (2 * reverseOrder m (lastBlock V) j + 1)) ≤
      V ^ (12 * (m + 1)) := by
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  change 2 ^ supportCost m (lastBlock V) ≤ _
  calc
    _ ≤ 2 ^ (12 * (m + 1) * 2 ^ lastBlock V) :=
      Nat.pow_le_pow_right (by norm_num) (supportCost_le_twelve m (lastBlock V))
    _ = (2 ^ (2 ^ lastBlock V)) ^ (12 * (m + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_left (lastBlock_lower_le V hV) _

theorem actualLowerCoefficient_support (V m : ℕ) (P : Finset ℕ) (hV : 2 ≤ V)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    {T : Finset ℕ} (hT : T ⊆ P) (hc : actualLowerCoefficient V m P T ≠ 0) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ V ^ (12 * (m + 1)) := by
  have hTu : T ⊆ (blockIndices V).biUnion (primeBlock P) := by
    simpa only [primeBlock_union V P hprime hsize] using hT
  have hbound := DisjointBlockExpansion.lowerCoefficient_prime_support (blockIndices V) (primeBlock P)
    (primeBlock_pairwise V P) (reverseOrder m (lastBlock V)) (fun j => 2 ^ (2 ^ (j + 1)))
    (fun j _ => Nat.one_le_pow _ _ (by norm_num))
    (fun j _ p hp => hprime p (Finset.mem_inter.mp hp).1)
    (fun j _ p hp => (mem_geometricPrimes.mp (Finset.mem_inter.mp hp).2).2.1.le) hTu hc
  exact ⟨hbound.1, hbound.2.trans (supportHeight_product_le V m hV)⟩

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FundamentalBlockEstimate
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FundamentalBlockEstimate

open scoped BigOperators

theorem product_upper_estimate (B : Finset ℕ) (V U δ : ℕ → ℝ)
    (hV : ∀ j ∈ B, 0 < V j) (hUlo : ∀ j ∈ B, V j ≤ U j)
    (hUhi : ∀ j ∈ B, U j ≤ (1 + δ j) * V j) :
    (∏ j ∈ B, V j) ≤ (∏ j ∈ B, U j) ∧
      (∏ j ∈ B, U j) ≤ (∏ j ∈ B, V j) * Real.exp (∑ j ∈ B, δ j) := by
  constructor
  · exact Finset.prod_le_prod (fun j hj => (hV j hj).le) hUlo
  · calc
      (∏ j ∈ B, U j) ≤ ∏ j ∈ B, V j * Real.exp (δ j) := by
        apply Finset.prod_le_prod
        · intro j hj
          exact (hV j hj).le.trans (hUlo j hj)
        · intro j hj
          apply (hUhi j hj).trans
          have h := Real.add_one_le_exp (δ j)
          simpa only [mul_comm, add_comm] using mul_le_mul_of_nonneg_left h (hV j hj).le
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum]

theorem correction_upper_estimate (B : Finset ℕ) (V U G δ : ℕ → ℝ)
    (hV : ∀ j ∈ B, 0 < V j) (hδ : ∀ j ∈ B, 0 ≤ δ j)
    (hUlo : ∀ j ∈ B, V j ≤ U j) (hUhi : ∀ j ∈ B, U j ≤ (1 + δ j) * V j)
    (hGhi : ∀ j ∈ B, G j ≤ δ j * V j) :
    (∑ j ∈ B, G j * ∏ i ∈ B.erase j, U i) ≤
      (∏ j ∈ B, V j) * (∑ j ∈ B, δ j) * Real.exp (∑ j ∈ B, δ j) := by
  classical
  have hVP : 0 < ∏ j ∈ B, V j := Finset.prod_pos hV
  calc
    _ ≤ ∑ j ∈ B, δ j * (∏ i ∈ B, V i) * Real.exp (∑ i ∈ B, δ i) := by
      apply Finset.sum_le_sum
      intro j hj
      have hEraseV : ∀ i ∈ B.erase j, 0 < V i := fun i hi => hV i (Finset.mem_of_mem_erase hi)
      have hEraseLo : ∀ i ∈ B.erase j, V i ≤ U i := fun i hi => hUlo i (Finset.mem_of_mem_erase hi)
      have hEraseHi : ∀ i ∈ B.erase j, U i ≤ (1 + δ i) * V i :=
        fun i hi => hUhi i (Finset.mem_of_mem_erase hi)
      have hEraseU := (product_upper_estimate (B.erase j) V U δ hEraseV hEraseLo hEraseHi).2
      have hEraseNonneg : 0 ≤ ∏ i ∈ B.erase j, U i :=
        Finset.prod_nonneg fun i hi => (hEraseV i hi).le.trans (hEraseLo i hi)
      have hS : (∑ i ∈ B.erase j, δ i) ≤ ∑ i ∈ B, δ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun i hi _ => hδ i hi)
      calc
        G j * (∏ i ∈ B.erase j, U i) ≤
            (δ j * V j) * ((∏ i ∈ B.erase j, V i) * Real.exp (∑ i ∈ B.erase j, δ i)) :=
          mul_le_mul (hGhi j hj) hEraseU hEraseNonneg (mul_nonneg (hδ j hj) (hV j hj).le)
        _ = δ j * (∏ i ∈ B, V i) * Real.exp (∑ i ∈ B.erase j, δ i) := by
          rw [← Finset.mul_prod_erase B V hj]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS) (mul_nonneg (hδ j hj) hVP.le)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

theorem exp_sub_one_le_self_mul_exp (S : ℝ) : Real.exp S - 1 ≤ S * Real.exp S := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-S)) (Real.exp_pos S).le
  have hexp : Real.exp S * Real.exp (-S) = 1 := by rw [← Real.exp_add]; simp
  rw [hexp] at h
  nlinarith

theorem global_relative_error (B : Finset ℕ) (V U G δ : ℕ → ℝ)
    (hV : ∀ j ∈ B, 0 < V j) (hδ : ∀ j ∈ B, 0 ≤ δ j)
    (hUlo : ∀ j ∈ B, V j ≤ U j) (hUhi : ∀ j ∈ B, U j ≤ (1 + δ j) * V j)
    (hGlo : ∀ j ∈ B, 0 ≤ G j) (hGhi : ∀ j ∈ B, G j ≤ δ j * V j) :
    |(∏ j ∈ B, U j) / (∏ j ∈ B, V j) - 1| ≤
        (∑ j ∈ B, δ j) * Real.exp (∑ j ∈ B, δ j) ∧
      |((∏ j ∈ B, U j) - ∑ j ∈ B, G j * ∏ i ∈ B.erase j, U i) /
          (∏ j ∈ B, V j) - 1| ≤
        (∑ j ∈ B, δ j) * Real.exp (∑ j ∈ B, δ j) := by
  have hVP : 0 < ∏ j ∈ B, V j := Finset.prod_pos hV
  have hS : 0 ≤ ∑ j ∈ B, δ j := Finset.sum_nonneg hδ
  have hE : 0 ≤ (∑ j ∈ B, δ j) * Real.exp (∑ j ∈ B, δ j) := mul_nonneg hS (Real.exp_pos _).le
  have hUpper := product_upper_estimate B V U δ hV hUlo hUhi
  have hCorr := correction_upper_estimate B V U G δ hV hδ hUlo hUhi hGhi
  have hCorr0 : 0 ≤ ∑ j ∈ B, G j * ∏ i ∈ B.erase j, U i := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (hGlo j hj)
    apply Finset.prod_nonneg
    intro i hi
    exact (hV i (Finset.mem_of_mem_erase hi)).le.trans (hUlo i (Finset.mem_of_mem_erase hi))
  have hUpperQlo : 1 ≤ (∏ j ∈ B, U j) / (∏ j ∈ B, V j) :=
    (le_div_iff₀ hVP).mpr (by simpa using hUpper.1)
  have hUpperQhi : (∏ j ∈ B, U j) / (∏ j ∈ B, V j) ≤ Real.exp (∑ j ∈ B, δ j) :=
    (div_le_iff₀ hVP).mpr (by nlinarith [hUpper.2])
  have hExp := exp_sub_one_le_self_mul_exp (∑ j ∈ B, δ j)
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    have hLowerQlo : 1 - (∑ j ∈ B, δ j) * Real.exp (∑ j ∈ B, δ j) ≤
        ((∏ j ∈ B, U j) - ∑ j ∈ B, G j * ∏ i ∈ B.erase j, U i) / (∏ j ∈ B, V j) := by
      apply (le_div_iff₀ hVP).mpr
      nlinarith [hUpper.1]
    have hLowerQhi : ((∏ j ∈ B, U j) - ∑ j ∈ B, G j * ∏ i ∈ B.erase j, U i) /
        (∏ j ∈ B, V j) ≤ Real.exp (∑ j ∈ B, δ j) := by
      apply (div_le_iff₀ hVP).mpr
      nlinarith [hUpper.2]
    constructor <;> nlinarith

theorem baseError_nonneg (m : ℕ) : 0 ≤ baseError m := by unfold baseError; positivity

theorem baseError_add (m t : ℕ) : baseError (m + t) = baseError m * (1 / 4 : ℝ) ^ t := by
  unfold baseError
  have hidx : 2 * (m + t) + 1 = (2 * m + 1) + 2 * t := by omega
  rw [hidx, pow_add, pow_mul, div_pow]
  norm_num
  field_simp

theorem sum_scheduled_error_le (m J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j)) ≤ 2 * baseError m := by
  simp only [PrimeDensityBlocks.reverseOrder, baseError_add, ← Finset.mul_sum]
  rw [Finset.sum_flip]
  have hgeom : (∑ j ∈ Finset.range (J + 1), (1 / 4 : ℝ) ^ j) ≤ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ ≤ _ := sum_geometric_two_le _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hgeom (baseError_nonneg m)

theorem six_baseError_le_exp (m : ℕ) (hm : 20000 ≤ m) :
    6 * baseError m ≤ Real.exp (-(m : ℝ) / 2) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hmR : (20000 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (2 : ℝ) ^ (2 * m + 1) = Real.exp (((2 * m + 1 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsix : (6 : ℝ) ≤ Real.exp 5 := by
    have h := Real.add_one_le_exp 5
    norm_num at h
    exact h
  unfold baseError
  calc
    6 * (Real.exp (5 * 1532) / (2 : ℝ) ^ (2 * m + 1)) ≤
        Real.exp 5 * (Real.exp (5 * 1532) / (2 : ℝ) ^ (2 * m + 1)) :=
      mul_le_mul_of_nonneg_right hsix (by positivity)
    _ = Real.exp (5 + 5 * 1532 - ((2 * m + 1 : ℕ) : ℝ) * Real.log 2) := by
      rw [← mul_div_assoc, ← Real.exp_add, hpow, ← Real.exp_sub]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (2 * m + 1))
      push_cast at hmul ⊢
      nlinarith

theorem scheduled_global_error_le_exp (m J : ℕ) (hm : 20000 ≤ m) :
    (∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j)) *
      Real.exp (∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j)) ≤
      Real.exp (-(m : ℝ) / 2) := by
  have hS := sum_scheduled_error_le m J
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j) :=
    Finset.sum_nonneg fun _ _ => baseError_nonneg _
  have hb := six_baseError_le_exp m hm
  have he1 : Real.exp (-(m : ℝ) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have h := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hS1 : (∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j)) ≤ 1 := by
    nlinarith [baseError_nonneg m]
  have hexp : Real.exp (∑ j ∈ Finset.range (J + 1), baseError (PrimeDensityBlocks.reverseOrder m J j)) ≤ 3 :=
    (Real.exp_le_exp.mpr hS1).trans Real.exp_one_lt_three.le
  calc
    _ ≤ (2 * baseError m) * 3 := mul_le_mul hS hexp (Real.exp_pos _).le (mul_nonneg (by norm_num) (baseError_nonneg m))
    _ = 6 * baseError m := by ring
    _ ≤ _ := hb

theorem actual_local_density_inputs (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    (hprime : ∀ p ∈ P, p.Prime) (hg0 : ∀ p ∈ P, 0 ≤ g p)
    (hdim : ∀ p ∈ P, g p ≤ 2 / p) (htwo : 2 ∈ P → g 2 ≤ 1 / 2) (j : ℕ) :
    0 < blockEuler P g j ∧
      blockEuler P g j ≤ blockUpperDensity V m P g j ∧
      blockUpperDensity V m P g j ≤
        (1 + baseError (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j)) * blockEuler P g j ∧
      0 ≤ blockOverflowDensity V m P g j ∧
      blockOverflowDensity V m P g j ≤
        baseError (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j) * blockEuler P g j := by
  let Q := PrimeDensityBlocks.primeBlock P j
  let t := PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j
  have hQ0 : ∀ p ∈ Q, 0 ≤ g p := fun p hp => hg0 p (Finset.mem_inter.mp hp).1
  have hcap := BonferroniDensity.prime_density_le_two_thirds P g hprime hdim htwo
  have hQ2 : ∀ p ∈ Q, g p ≤ 2 / 3 := fun p hp => hcap p (Finset.mem_inter.mp hp).1
  have hsum : (∑ p ∈ Q, g p) ≤ 1532 := PrimeDensityBlocks.primeBlock_density_sum_le P j g hdim
  have heuler := BonferroniDensity.exp_neg_three_mul_le_eulerProduct Q g hQ0 hQ2 hsum
  have hpos : 0 < ∏ p ∈ Q, (1 - g p) := (Real.exp_pos _).trans_le heuler
  have hrel := BonferroniDensity.densityPolynomial_relative_error Q g hQ0 hQ2 (by norm_num) hsum t
  have hbound := BonferroniDensity.densityPolynomial_bounds Q g hQ0 (fun p hp => by linarith [hQ2 p hp]) t
  have htail := BonferroniDensity.relative_elementarySum_le_exponential Q g hQ0 hQ2 (by norm_num) hsum (2 * t + 1)
  refine ⟨hpos, hbound.2, ?_, BonferroniDensity.elementarySum_nonneg Q g hQ0 _, ?_⟩
  · change BonferroniDensity.densityPolynomial (2 * t) Q g ≤ (1 + baseError t) * (∏ p ∈ Q, (1 - g p))
    apply (div_le_iff₀ hpos).mp
    have h := (abs_le.mp hrel.1).2
    change BonferroniDensity.densityPolynomial (2 * t) Q g / (∏ p ∈ Q, (1 - g p)) - 1 ≤ baseError t at h
    linarith
  · exact (div_le_iff₀ hpos).mp htail

theorem actual_global_density_error (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    (hm : 20000 ≤ m) (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |actualUpperDensity V m P g / (∏ p ∈ P, (1 - g p)) - 1| ≤ Real.exp (-(m : ℝ) / 2) ∧
      |actualLowerDensity V m P g / (∏ p ∈ P, (1 - g p)) - 1| ≤ Real.exp (-(m : ℝ) / 2) := by
  let B := PrimeDensityBlocks.blockIndices V
  let blocks := PrimeDensityBlocks.primeBlock P
  let orders := PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V)
  have hdis := PrimeDensityBlocks.primeBlock_pairwise V P
  have hunion := PrimeDensityBlocks.primeBlock_union V P hprime hsize
  have hloc := actual_local_density_inputs V m P g hprime hg0 hdim htwo
  have hglob := global_relative_error B (blockEuler P g) (blockUpperDensity V m P g)
    (blockOverflowDensity V m P g) (fun j => baseError (orders j))
    (fun j _ => (hloc j).1) (fun j _ => baseError_nonneg _) (fun j _ => (hloc j).2.1)
    (fun j _ => (hloc j).2.2.1) (fun j _ => (hloc j).2.2.2.1) (fun j _ => (hloc j).2.2.2.2)
  have hError := scheduled_global_error_le_exp m (PrimeDensityBlocks.lastBlock V) hm
  have hEuler : (∏ j ∈ B, blockEuler P g j) = ∏ p ∈ P, (1 - g p) := by
    change (∏ j ∈ B, ∏ p ∈ blocks j, (1 - g p)) = _
    rw [← Finset.prod_biUnion hdis, hunion]
  have hUpper : actualUpperDensity V m P g = ∏ j ∈ B, blockUpperDensity V m P g j := by
    have h := DisjointBlockExpansion.upperCoefficient_density B blocks hdis orders g
    rw [hunion] at h
    exact h
  have hLower : actualLowerDensity V m P g =
      (∏ j ∈ B, blockUpperDensity V m P g j) -
        ∑ j ∈ B, blockOverflowDensity V m P g j * ∏ i ∈ B.erase j, blockUpperDensity V m P g i := by
    have h := DisjointBlockExpansion.lowerCoefficient_density B blocks hdis orders g
    rw [hunion] at h
    exact h
  rw [hUpper, hLower, ← hEuler]
  exact ⟨hglob.1.trans hError, hglob.2.trans hError⟩

theorem actualUpperCoefficient_support (V m : ℕ) (P : Finset ℕ) (hV : 2 ≤ V)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    {T : Finset ℕ} (hT : T ⊆ P) (hc : actualUpperCoefficient V m P T ≠ 0) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ V ^ (12 * (m + 1)) := by
  have hTu : T ⊆ (PrimeDensityBlocks.blockIndices V).biUnion (PrimeDensityBlocks.primeBlock P) := by
    simpa only [PrimeDensityBlocks.primeBlock_union V P hprime hsize] using hT
  have hbound := DisjointBlockExpansion.prime_product_support (PrimeDensityBlocks.blockIndices V)
    (PrimeDensityBlocks.primeBlock P) (PrimeDensityBlocks.primeBlock_pairwise V P)
    (fun j => 2 * PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j + 1)
    (fun j => 2 ^ (2 ^ (j + 1))) (fun j _ => Nat.one_le_pow _ _ (by norm_num))
    (fun j _ p hp => hprime p (Finset.mem_inter.mp hp).1)
    (fun j _ p hp => (PrimeDensityBlocks.mem_geometricPrimes.mp (Finset.mem_inter.mp hp).2).2.1.le)
    hTu (fun j hj => (DisjointBlockExpansion.upperCoefficient_card hc j hj).trans (Nat.le_succ _))
  exact ⟨hbound.1, hbound.2.trans (PrimeDensityBlocks.supportHeight_product_le V m hV)⟩

theorem coefficient_remainder_level_bound (P : Finset ℕ) (L : ℕ) (coeff E : Finset ℕ → ℝ)
    (hc : ∀ T ∈ P.powerset, |coeff T| ≤ 1)
    (hlevel : ∀ T ∈ P.powerset, coeff T ≠ 0 → (∏ p ∈ T, p) ≤ L) :
    |∑ T ∈ P.powerset, coeff T * E T| ≤ ∑ T ∈ levelSubsets P L, |E T| := by
  classical
  apply (DisjointBlockExpansion.supported_remainder_bound P coeff E hc).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨hTP, hnz⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨hTP, hlevel T hTP hnz⟩
  · intro T _ _
    exact abs_nonneg _

theorem additive_bounds_of_relative {D E ε : ℝ} (hE : 0 < E) (h : |D / E - 1| ≤ ε) :
    E - E * ε ≤ D ∧ D ≤ E + E * ε := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  have hDlo : (1 - ε) * E ≤ D := (le_div_iff₀ hE).mp (by linarith)
  have hDhi : D ≤ (1 + ε) * E := (div_le_iff₀ hE).mp (by linarith)
  constructor <;> nlinarith

theorem finite_fundamental_lemma {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (V m : ℕ) (P : Finset ℕ) (X : ℝ) (g : ℕ → ℝ)
    (hV : 2 ≤ V) (hm : 20000 ≤ m) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |(∑ x ∈ C, weight x * BonferroniBlocks.survives P (fun p => hit p x)) -
        X * (∏ p ∈ P, (1 - g p))| ≤
      X * (∏ p ∈ P, (1 - g p)) * Real.exp (-(m : ℝ) / 2) +
        ∑ T ∈ levelSubsets P (V ^ (12 * (m + 1))),
          |BonferroniBlocks.intersectionRemainder C weight hit X g T| := by
  let cU := actualUpperCoefficient V m P
  let cL := PrimeDensityBlocks.actualLowerCoefficient V m P
  let E := BonferroniBlocks.intersectionRemainder C weight hit X g
  have hcap := BonferroniDensity.prime_density_le_two_thirds P g hprime hdim htwo
  have hEuler : 0 < ∏ p ∈ P, (1 - g p) := Finset.prod_pos (fun p hp => by linarith [hcap p hp])
  have hDensity := actual_global_density_error V m P g hm hprime hsize hg0 hdim htwo
  have hUmain := additive_bounds_of_relative hEuler hDensity.1
  have hLmain := additive_bounds_of_relative hEuler hDensity.2
  have hRU := coefficient_remainder_level_bound P (V ^ (12 * (m + 1))) cU E
    (fun T _ => DisjointBlockExpansion.upperCoefficient_abs_le _ _ _ _)
    (fun T hT hnz => (actualUpperCoefficient_support V m P hV hprime hsize
      (Finset.mem_powerset.mp hT) hnz).2)
  have hRL := coefficient_remainder_level_bound P (V ^ (12 * (m + 1))) cL E
    (fun T _ => DisjointBlockExpansion.lowerCoefficient_abs_le _ _ _ _)
    (fun T hT hnz => (PrimeDensityBlocks.actualLowerCoefficient_support V m P hV hprime hsize
      (Finset.mem_powerset.mp hT) hnz).2)
  have hUdecomp := DisjointBlockExpansion.global_main_remainder C weight hit P cU X g
  have hLdecomp := DisjointBlockExpansion.global_main_remainder C weight hit P cL X g
  have hcounts := DisjointBlockExpansion.weighted_global_coefficient_bounds C weight hweight hit
    (PrimeDensityBlocks.blockIndices V) (PrimeDensityBlocks.primeBlock P)
    (PrimeDensityBlocks.primeBlock_pairwise V P)
    (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V))
  rw [PrimeDensityBlocks.primeBlock_union V P hprime hsize] at hcounts
  change (∑ T ∈ P.powerset, cL T * BonferroniBlocks.intersectionMass C weight hit T) ≤ _ ∧
    _ ≤ (∑ T ∈ P.powerset, cU T * BonferroniBlocks.intersectionMass C weight hit T) at hcounts
  rw [hUdecomp, hLdecomp] at hcounts
  change X * actualLowerDensity V m P g + (∑ T ∈ P.powerset, cL T * E T) ≤ _ ∧
    _ ≤ X * actualUpperDensity V m P g + (∑ T ∈ P.powerset, cU T * E T) at hcounts
  have hLo := mul_le_mul_of_nonneg_left hLmain.1 hX
  have hHi := mul_le_mul_of_nonneg_left hUmain.2 hX
  have hRLo := (abs_le.mp hRL).1
  have hRHi := (abs_le.mp hRU).2
  rw [abs_le]
  constructor <;> nlinarith

theorem remainder_sum_eq_divisors {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (P : Finset ℕ) (L : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ T ∈ levelSubsets P L, |BonferroniBlocks.intersectionRemainder C weight hit X g T|) =
      ∑ d ∈ levelDivisors P L, |integerRemainder C weight hit X g d| := by
  classical
  have hsq : Squarefree (∏ p ∈ P, p) := IntervalBoundingSieve.squarefree_primeSet_product P hprime
  have hPfac : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hprime
  apply Finset.sum_bij (fun T _ => ∏ p ∈ T, p)
  · intro T hT
    obtain ⟨hTP, hTL⟩ := Finset.mem_filter.mp hT
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr
      ⟨Finset.prod_dvd_prod_of_subset T P id (Finset.mem_powerset.mp hTP), hsq.ne_zero⟩, hTL⟩
  · intro T hT U hU hEq
    exact DisjointBlockExpansion.prime_product_injective P hprime
      (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hU).1 hEq
  · intro d hd
    obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
    have hdiv := Nat.dvd_of_mem_divisors hdP
    have hdsq := hsq.squarefree_of_dvd hdiv
    have hsub : d.primeFactors ⊆ P := by
      rw [← hPfac]
      exact Nat.primeFactors_mono hdiv hsq.ne_zero
    have hprod : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsq
    exact ⟨d.primeFactors, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hsub, by simpa only [hprod] using hdL⟩, hprod⟩
  · intro T hT
    have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hfac : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod (fun p hp => hprime p (hTP hp))
    simp only [integerRemainder, hfac]

theorem finite_fundamental_integer_level {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (V m : ℕ) (P : Finset ℕ) (X : ℝ) (g : ℕ → ℝ)
    (hV : 2 ≤ V) (hm : 20000 ≤ m) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |(∑ x ∈ C, weight x * BonferroniBlocks.survives P (fun p => hit p x)) -
        X * (∏ p ∈ P, (1 - g p))| ≤
      X * (∏ p ∈ P, (1 - g p)) * Real.exp (-(m : ℝ) / 2) +
        ∑ d ∈ levelDivisors P (V ^ (12 * (m + 1))), |integerRemainder C weight hit X g d| := by
  have h := finite_fundamental_lemma C weight hweight hit V m P X g hV hm hX hprime hsize hg0 hdim htwo
  rw [remainder_sum_eq_divisors C weight hit X g P _ hprime] at h
  exact h

theorem fundamental_integer_parameter {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (V s : ℕ) (P : Finset ℕ) (X : ℝ) (g : ℕ → ℝ)
    (hV : 2 ≤ V) (hs : 240012 ≤ s) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |(∑ x ∈ C, weight x * BonferroniBlocks.survives P (fun p => hit p x)) -
        X * (∏ p ∈ P, (1 - g p))| ≤
      X * (∏ p ∈ P, (1 - g p)) * Real.exp (-(s : ℝ) / 48) +
        ∑ d ∈ levelDivisors P (V ^ s), |integerRemainder C weight hit X g d| := by
  let m := s / 12 - 1
  have hm : 20000 ≤ m := by dsimp [m]; omega
  have hlevel : 12 * (m + 1) ≤ s := by dsimp [m]; omega
  have hms : s ≤ 24 * m := by dsimp [m]; omega
  have h := finite_fundamental_integer_level C weight hweight hit V m P X g hV hm hX hprime hsize hg0 hdim htwo
  apply h.trans
  apply add_le_add
  · have hcap := BonferroniDensity.prime_density_le_two_thirds P g hprime hdim htwo
    have hEuler : 0 ≤ ∏ p ∈ P, (1 - g p) := Finset.prod_nonneg (fun p hp => by linarith [hcap p hp])
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX hEuler)
    apply Real.exp_le_exp.mpr
    have hmsR : (s : ℝ) ≤ 24 * (m : ℝ) := by exact_mod_cast hms
    linarith
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hdP, hdL.trans (Nat.pow_le_pow_right (by omega) hlevel)⟩
    · intro d _ _
      exact abs_nonneg _

end NumberTheoryLean.FundamentalBlockEstimate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RealFundamentalSieve

open scoped BigOperators

theorem floor_level_le (v s : ℝ) (hv : 1 ≤ v) (hs : 0 ≤ s) :
    (((⌊v⌋₊ ^ ⌊s⌋₊ : ℕ) : ℝ)) ≤ v ^ s := by
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (⌊v⌋₊ : ℝ) ^ (⌊s⌋₊ : ℝ) ≤ v ^ (⌊s⌋₊ : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (Nat.cast_nonneg _)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hv (Nat.floor_le hs)

theorem fundamental_lemma {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (v s : ℝ) (P : Finset ℕ) (X : ℝ) (g : ℕ → ℝ)
    (hv : 2 ≤ v) (hs : 480024 ≤ s) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p : ℝ) ≤ v)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |(∑ x ∈ C, weight x * BonferroniBlocks.survives P (fun p => hit p x)) -
        X * (∏ p ∈ P, (1 - g p))| ≤
      X * (∏ p ∈ P, (1 - g p)) * Real.exp (-s / 96) +
        ∑ d ∈ levelDivisors P v s, |FundamentalBlockEstimate.integerRemainder C weight hit X g d| := by
  have hv0 : 0 ≤ v := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hV : 2 ≤ ⌊v⌋₊ := (Nat.le_floor_iff hv0).mpr (by exact_mod_cast hv)
  have hS : 240012 ≤ ⌊s⌋₊ := (Nat.le_floor_iff hs0).mpr (by norm_num <;> linarith)
  have hPsize : ∀ p ∈ P, p ≤ ⌊v⌋₊ := fun p hp => (Nat.le_floor_iff hv0).mpr (hsize p hp)
  have h := FundamentalBlockEstimate.fundamental_integer_parameter C weight hweight hit
    ⌊v⌋₊ ⌊s⌋₊ P X g hV hS hX hprime hPsize hg0 hdim htwo
  apply h.trans
  apply add_le_add
  · have hcap := BonferroniDensity.prime_density_le_two_thirds P g hprime hdim htwo
    have hEuler : 0 ≤ ∏ p ∈ P, (1 - g p) := Finset.prod_nonneg (fun p hp => by linarith [hcap p hp])
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX hEuler)
    apply Real.exp_le_exp.mpr
    have hfloor := Nat.lt_floor_add_one s
    linarith
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
      apply Finset.mem_filter.mpr
      refine ⟨hdP, ?_⟩
      have hdLReal : (d : ℝ) ≤ ((⌊v⌋₊ ^ ⌊s⌋₊ : ℕ) : ℝ) := by exact_mod_cast hdL
      exact hdLReal.trans (floor_level_le v s (by linarith) hs0)
    · intro d _ _
      exact abs_nonneg _

end NumberTheoryLean.RealFundamentalSieve

end

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped BigOperators

theorem squarefree_dvd_iff_primeFactors {d x : ℕ} (hd : Squarefree d) :
    d ∣ x ↔ ∀ p ∈ d.primeFactors, p ∣ x := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    · rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hx]
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp, hx⟩

theorem intersectionValue_divisibility (A i d : ℕ) (hd : Squarefree d) :
    BonferroniBlocks.intersectionValue d.primeFactors (fun p => p ∣ A + i) =
      (if d ∣ A + i then 1 else 0 : ℝ) := by
  classical
  unfold BonferroniBlocks.intersectionValue
  simp only [← squarefree_dvd_iff_primeFactors hd]

theorem reciprocal_primeFactors_product {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, (p : ℝ)⁻¹) = (d : ℝ)⁻¹ := by
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

theorem integerRemainder_eq_interval_rem (A N D : ℕ) (hD : Squarefree D)
    {d : ℕ} (hd : d ∣ D) :
    FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) (N : ℝ) (fun p => (p : ℝ)⁻¹) d =
      (IntervalBoundingSieve.intervalSieve A N D hD).rem d := by
  classical
  have hdsq : Squarefree d := hD.squarefree_of_dvd hd
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    BonferroniBlocks.intersectionMass
  simp_rw [one_mul, intersectionValue_divisibility A _ d hdsq]
  rw [reciprocal_primeFactors_product hdsq]
  change (∑ i ∈ Finset.range N, if d ∣ A + i then (1 : ℝ) else 0) -
      (N : ℝ) * (d : ℝ)⁻¹ = _
  rw [BoundingSieve.rem, IntervalBoundingSieve.interval_multSum]
  simp only [LargePrimeDeletion.deletionCell, ← Nat.cast_add, Int.natCast_dvd_natCast,
    Finset.sum_boole, IntervalBoundingSieve.intervalSieve, IntervalBoundingSieve.reciprocalDensity_apply]
  ring

theorem integerRemainder_abs_le_two (A N D : ℕ) (hD : Squarefree D)
    {d : ℕ} (hd : d ∣ D) (J : ℝ) (hNJ : |(N : ℝ) - J| ≤ 1) :
    |FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) J (fun p => (p : ℝ)⁻¹) d| ≤ 2 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hD.ne_zero)
  have hdsq : Squarefree d := hD.squarefree_of_dvd hd
  have hEq : FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) J (fun p => (p : ℝ)⁻¹) d =
      (IntervalBoundingSieve.intervalSieve A N D hD).rem d + ((N : ℝ) - J) * (d : ℝ)⁻¹ := by
    rw [← integerRemainder_eq_interval_rem A N D hD hd]
    unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    rw [reciprocal_primeFactors_product hdsq]
    ring
  rw [hEq]
  have hInv : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hdpos)
  have hErr : |((N : ℝ) - J) * (d : ℝ)⁻¹| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg d))]
    simpa only [one_mul] using mul_le_mul hNJ hInv (inv_nonneg.mpr (Nat.cast_nonneg d)) zero_le_one
  exact (abs_add_le _ _).trans (by linarith [IntervalBoundingSieve.interval_rem_abs_le_one A N D hD hdpos])

theorem survives_sum_eq_coprimeOffsets (A N : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ i ∈ Finset.range N, (1 : ℝ) * BonferroniBlocks.survives P (fun p => p ∣ A + i)) =
      ((LargePrimeDeletion.coprimeOffsets N (∏ p ∈ P, p) (A : ℤ)).card : ℝ) := by
  classical
  have hD : Squarefree (∏ p ∈ P, p) := IntervalBoundingSieve.squarefree_primeSet_product P hprime
  have hfac : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hprime
  have hpoint : ∀ i : ℕ, BonferroniBlocks.survives P (fun p => p ∣ A + i) =
      if (A + i).Coprime (∏ p ∈ P, p) then 1 else 0 := by
    intro i
    unfold BonferroniBlocks.survives
    have hcop := LargePrimeDeletion.coprime_iff_avoid_primeFactors
      (Nat.pos_of_ne_zero hD.ne_zero) ((A + i : ℕ) : ℤ)
    simp only [hfac, Int.natAbs_natCast, Int.natCast_dvd_natCast] at hcop
    simp only [← hcop]
  simp_rw [one_mul, hpoint]
  simp only [LargePrimeDeletion.coprimeOffsets, ← Nat.cast_add, Int.natAbs_natCast, Finset.sum_boole]

theorem realLevelDivisors_card_le (P : Finset ℕ) (u s : ℝ) (hu : 0 ≤ u) :
    ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) ≤ u ^ s := by
  classical
  have hpow : 0 ≤ u ^ s := Real.rpow_nonneg hu s
  have hsub : RealFundamentalSieve.levelDivisors P u s ⊆ Finset.Icc 1 ⌊u ^ s⌋₊ := by
    intro d hd
    obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, (Nat.le_floor_iff hpow).mpr hdL⟩
  have hcard : (RealFundamentalSieve.levelDivisors P u s).card ≤ ⌊u ^ s⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  exact (show ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) ≤ (⌊u ^ s⌋₊ : ℝ) by exact_mod_cast hcard).trans
    (Nat.floor_le hpow)

theorem cutoffSurvivors_eq_residueAvoidingOffsets (N z : ℕ) (residue : ℕ → ℕ) :
    LargePrimeDeletion.cutoffSurvivors N z residue =
      IntervalBoundingSieve.residueAvoidingOffsets N (IntervalBoundingSieve.cutoffProduct z) residue := by
  classical
  ext i
  simp only [LargePrimeDeletion.mem_cutoffSurvivors, IntervalBoundingSieve.residueAvoidingOffsets,
    Finset.mem_filter, Finset.mem_range, IntervalBoundingSieve.cutoffProduct_primeFactors,
    LargePrimeDeletion.mem_cutoffPrimes]
  tauto

theorem finite_small_sieve_bound (N : ℕ) (u s J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hs : 480024 ≤ s) (hJ : 0 ≤ J) (hNJ : |(N : ℝ) - J| ≤ 1) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) - J * smallEuler ⌊u⌋₊| ≤
      J * smallEuler ⌊u⌋₊ * Real.exp (-s / 96) + 2 * u ^ s := by
  classical
  let z := ⌊u⌋₊
  let P := LargePrimeDeletion.cutoffPrimes z
  let D := IntervalBoundingSieve.cutoffProduct z
  have hD : Squarefree D := IntervalBoundingSieve.cutoffProduct_squarefree z
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1
  have hsize : ∀ p ∈ P, (p : ℝ) ≤ u := by
    intro p hp
    have hpz := (LargePrimeDeletion.mem_cutoffPrimes.mp hp).2
    exact (show (p : ℝ) ≤ (z : ℝ) by exact_mod_cast hpz).trans (Nat.floor_le (by linarith))
  obtain ⟨A, hA⟩ := IntervalBoundingSieve.exists_residue_count_translation N D
    (Nat.pos_of_ne_zero hD.ne_zero) residue
  have hcount : (LargePrimeDeletion.cutoffSurvivors N z residue).card =
      (LargePrimeDeletion.coprimeOffsets N D (A : ℤ)).card := by
    rw [cutoffSurvivors_eq_residueAvoidingOffsets, hA]
  have h := RealFundamentalSieve.fundamental_lemma (Finset.range N) (fun _ => (1 : ℝ))
    (fun _ _ => by norm_num) (fun p i => p ∣ A + i) u s P J (fun p => (p : ℝ)⁻¹)
    hu hs hJ hprime hsize (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun p _ => by simpa only [one_div] using
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_nonneg p))
    (fun _ => by norm_num)
  rw [survives_sum_eq_coprimeOffsets A N P hprime] at h
  change |((LargePrimeDeletion.coprimeOffsets N D (A : ℤ)).card : ℝ) - J * smallEuler z| ≤ _ at h
  rw [← hcount] at h
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _d ∈ RealFundamentalSieve.levelDivisors P u s, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact integerRemainder_abs_le_two A N D hD
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) J hNJ
    _ = 2 * ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) := by simp [mul_comm]
    _ ≤ 2 * u ^ s := mul_le_mul_of_nonneg_left (realLevelDivisors_card_le P u s (by linarith)) (by norm_num)

theorem all_integer_euler_product (z : ℕ) (hz : 1 ≤ z) :
    (∏ n ∈ Finset.Icc 2 z, (1 - (n : ℝ)⁻¹)) = (z : ℝ)⁻¹ := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
      have hzs : ((z + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem smallEuler_ge_inv (z : ℕ) (hz : 2 ≤ z) : (z : ℝ)⁻¹ ≤ smallEuler z := by
  have hsubset : LargePrimeDeletion.cutoffPrimes z ⊆ Finset.Icc 2 z := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, hpz⟩
  rw [← all_integer_euler_product z (by omega)]
  apply Finset.prod_le_prod_of_subset_of_le_one hsubset
  · intro n hn
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega))
  · intro n _ _
    have h := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n)
    linarith

theorem smallEuler_floor_ge_inv (u : ℝ) (hu : 2 ≤ u) : u⁻¹ ≤ smallEuler ⌊u⌋₊ := by
  have hz : 2 ≤ ⌊u⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  have hzpos : (0 : ℝ) < (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊u⌋₊ by omega)
  exact ((inv_le_inv₀ (by linarith) hzpos).mpr (Nat.floor_le (by linarith))).trans (smallEuler_ge_inv _ hz)

end NumberTheoryLean.SmallSieveFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueCountDifference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.ProgressionSieve

open scoped BigOperators

theorem exists_affine_residue {p q : ℕ} (hp : p.Prime) (hqp : q.Coprime p)
    (r c : ℕ) : ∃ b : ℕ, ∀ t : ℕ,
      (r + q * t) % p = c % p ↔ t % p = b % p := by
  obtain ⟨b, _, hb⟩ := Nat.exists_mul_mod_eq_of_coprime (p - r % p + c) hqp hp.ne_zero
  have hsol : Nat.ModEq p (r + q * b) c := by
    have h := (Nat.mod_modEq r p).symm.add (show Nat.ModEq p (q * b) (p - r % p + c) from hb)
    have heq : r % p + (p - r % p + c) = p + c := by
      have := Nat.mod_lt r hp.pos
      omega
    rw [heq] at h
    exact h.trans (show Nat.ModEq p (p + c) c by simp [Nat.ModEq])
  refine ⟨b, ?_⟩
  intro t
  constructor
  · intro h
    have hprod := Nat.ModEq.add_left_cancel' r ((show Nat.ModEq p (r + q * t) c from h).trans hsol.symm)
    exact hprod.cancel_left_of_coprime hqp.symm.gcd_eq_one
  · intro h
    exact ((show Nat.ModEq p t b from h).mul_left q |>.add_left r).trans hsol

end NumberTheoryLean.ProgressionSieve



namespace NumberTheoryLean.SmallSieveRelative

open scoped BigOperators

theorem normalized_remainder_le (u v : ℝ) (hu : 2 ≤ u) (hv : 4 ≤ v) :
    u ^ (v / 2) / (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) ≤ Real.exp (-v / 192) := by
  have hu0 : 0 < u := by linarith
  have hJ : 0 < u ^ v := Real.rpow_pos_of_pos hu0 v
  have hEuler := SmallSieveFinite.smallEuler_floor_ge_inv u hu
  have hinv : 0 < u⁻¹ := inv_pos.mpr hu0
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogu : (1 / 2 : ℝ) ≤ Real.log u := hlog2.trans (Real.log_le_log (by norm_num) hu)
  calc
    u ^ (v / 2) / (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) ≤
        u ^ (v / 2) / (u ^ v * u⁻¹) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hu0.le _) (mul_pos hJ hinv)
        (mul_le_mul_of_nonneg_left hEuler hJ.le)
    _ = (u ^ (v / 2) / u ^ v) * u := by field_simp
    _ = u ^ (v / 2 - v) * u := by rw [Real.rpow_sub hu0]
    _ = u ^ (1 - v / 2) := by
      have hidx : (v / 2 - v) + 1 = 1 - v / 2 := by ring
      rw [← hidx, Real.rpow_add hu0, Real.rpow_one]
    _ = Real.exp (Real.log u * (1 - v / 2)) := Real.rpow_def_of_pos hu0 _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg (show 0 ≤ v / 2 - 1 by linarith) (sub_nonneg.mpr hlogu)
      nlinarith

theorem relative_bound_rpow (N : ℕ) (u v : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hv : 960048 ≤ v) (hNJ : |(N : ℝ) - u ^ v| ≤ 1) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) /
        (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤ 3 * Real.exp (-v / 192) := by
  have hu0 : 0 < u := by linarith
  have hJ : 0 < u ^ v := Real.rpow_pos_of_pos hu0 v
  have hEuler : 0 < SmallSieveFinite.smallEuler ⌊u⌋₊ :=
    (inv_pos.mpr hu0).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv u hu)
  have hDen : 0 < u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊ := mul_pos hJ hEuler
  have h := SmallSieveFinite.finite_small_sieve_bound N u (v / 2) (u ^ v) residue
    hu (by linarith) hJ.le hNJ
  have hparam : -(v / 2) / 96 = -v / 192 := by ring
  rw [hparam] at h
  have hrem := normalized_remainder_le u v hu (by linarith)
  let A : ℝ := (LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card
  let D : ℝ := u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊
  have hD0 : D ≠ 0 := ne_of_gt hDen
  have hEq : A / D - 1 = (A - D) / D := by field_simp [hD0]
  change |A / D - 1| ≤ _
  rw [hEq, abs_div, abs_of_pos hDen]
  calc
    |A - D| / D ≤ (D * Real.exp (-v / 192) + 2 * u ^ (v / 2)) / D :=
      div_le_div_of_nonneg_right h hDen.le
    _ = Real.exp (-v / 192) + 2 * (u ^ (v / 2) / D) := by field_simp [hD0]
    _ ≤ _ := by change u ^ (v / 2) / D ≤ _ at hrem; linarith

theorem rpow_log_ratio (u J : ℝ) (hu : 1 < u) (hJ : 0 < J) :
    u ^ (Real.log J / Real.log u) = J := by
  have hlu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu)
  rw [Real.rpow_def_of_pos (by linarith)]
  have he : Real.log u * (Real.log J / Real.log u) = Real.log J := by field_simp
  rw [he, Real.exp_log hJ]

theorem small_relative (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) /
        (J * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤
      3 * Real.exp (-(Real.log J / Real.log u) / 192) := by
  have hpow := rpow_log_ratio u J (by linarith) hJ
  have h := relative_bound_rpow N u (Real.log J / Real.log u) residue hu hv (by simpa only [hpow] using hNJ)
  simpa only [hpow] using h

end NumberTheoryLean.SmallSieveRelative



namespace NumberTheoryLean.ProgressionSmallSieve

theorem exists_integer_affine_residue (a : ℤ) (q c : ℕ) {p : ℕ}
    (hp : p.Prime) (hqp : q.Coprime p) : ∃ b : ℕ, ∀ i : ℕ,
      Int.ModEq (p : ℤ) (a + (q : ℤ) * i) (c : ℤ) ↔ Nat.ModEq p i b := by
  let r : ℕ := (a % p).toNat
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hr : (r : ℤ) = a % p := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpz))
  have ha : Int.ModEq (p : ℤ) a r := by
    unfold Int.ModEq
    rw [hr, Int.emod_emod]
  obtain ⟨b, hb⟩ := ProgressionSieve.exists_affine_residue hp hqp r c
  refine ⟨b, ?_⟩
  intro i
  have hshift : Int.ModEq (p : ℤ) (a + (q : ℤ) * i) ((r + q * i : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using ha.add_right ((q : ℤ) * i)
  constructor
  · intro h
    have hnat : Nat.ModEq p (r + q * i) c := Int.natCast_modEq_iff.mp (hshift.symm.trans h)
    exact (hb i).mp hnat
  · intro h
    have hnat : Nat.ModEq p (r + q * i) c := (hb i).mpr h
    exact hshift.trans (Int.natCast_modEq_iff.mpr hnat)

theorem exists_coordinate_residues (z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hcoprime : ∀ p : ℕ, p.Prime → p ≤ z → q.Coprime p) :
    ∃ transformed : ℕ → ℕ, ∀ p, p.Prime → p ≤ z → ∀ i : ℕ,
      progressionHit a q residue p i ↔ SievePartition.residueBad transformed p i := by
  classical
  have hchoice : ∀ p : ℕ, ∃ b : ℕ, p.Prime → p ≤ z → ∀ i : ℕ,
      progressionHit a q residue p i ↔ Nat.ModEq p i b := by
    intro p
    by_cases hp : p.Prime ∧ p ≤ z
    · obtain ⟨b, hb⟩ := exists_integer_affine_residue a q (residue p) hp.1 (hcoprime p hp.1 hp.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun hprime hpz => False.elim (hp ⟨hprime, hpz⟩)⟩
  choose transformed htrans using hchoice
  exact ⟨transformed, htrans⟩

theorem exists_progressionSurvivors_eq (N z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hcoprime : ∀ p : ℕ, p.Prime → p ≤ z → q.Coprime p) :
    ∃ transformed : ℕ → ℕ,
      progressionSurvivors N z a q residue = LargePrimeDeletion.cutoffSurvivors N z transformed := by
  classical
  obtain ⟨transformed, htrans⟩ := exists_coordinate_residues z a q residue hcoprime
  refine ⟨transformed, ?_⟩
  ext i
  simp only [progressionSurvivors, LargePrimeDeletion.cutoffSurvivors, SievePartition.mem_survivors]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro p hp
  obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
  exact not_congr (htrans p hprime hpz i)

theorem progression_small_relative (N : ℕ) (u J : ℝ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u)
    (hcoprime : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ u → q.Coprime p) :
    |((progressionSurvivors N ⌊u⌋₊ a q residue).card : ℝ) /
        (J * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤
      3 * Real.exp (-(Real.log J / Real.log u) / 192) := by
  have hcop : ∀ p, p.Prime → p ≤ ⌊u⌋₊ → q.Coprime p := by
    intro p hp hpz
    exact hcoprime p hp ((Nat.le_floor_iff (by linarith)).mp hpz)
  obtain ⟨transformed, hEq⟩ := exists_progressionSurvivors_eq N ⌊u⌋₊ a q residue hcop
  rw [hEq]
  exact SmallSieveRelative.small_relative N u J transformed hu hJ hNJ hv

end NumberTheoryLean.ProgressionSmallSieve



namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean
attribute [local instance] Classical.propDecidable

theorem modulus_candidates_eq_offsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) :
    modulusCandidates Y small a d =
      (modulusOffsets Y small a d hd).image (fun j => primeHitRepresentative d hd a+d*j) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hb := primeHitRepresentative_spec d hd a
  ext n
  rw [mem_modulusCandidates]
  simp only [modulusOffsets,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hn1,hnY,hpr,hsmall⟩
    obtain ⟨j,rfl⟩ := exists_positive_coordinate d _ n hd0 hb.1 hb.2.1 hn1 ((hb.2.2 n).mp hpr)
    exact ⟨j,⟨(lt_hitLength_iff Y d _ j hd0 hb.2.1).mpr hnY,hsmall⟩,rfl⟩
  · rintro ⟨j,⟨hj,hsmall⟩,rfl⟩
    refine ⟨by omega,(lt_hitLength_iff Y d _ j hd0 hb.2.1).mp hj,?_,hsmall⟩
    apply (hb.2.2 _).mpr
    change (_+d*j)%d=_%d
    simp

theorem modulus_count_eq_offsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) :
    modulusCount Y small a d = ((modulusOffsets Y small a d hd).card : ℤ) := by
  unfold modulusCount
  rw [modulus_candidates_eq_offsets,Finset.card_image_of_injective]
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd.ne_zero) (Nat.add_left_cancel hij)

theorem offsets_eq_progression (Y z : ℕ) (a : ℕ → ℕ) (d : ℕ) (hd : Squarefree d) :
    modulusOffsets Y (LargePrimeDeletion.cutoffPrimes z) a d hd =
      ProgressionSmallSieve.progressionSurvivors (hitLength Y d (primeHitRepresentative d hd a))
        z (primeHitRepresentative d hd a : ℤ) d a := by
  ext j
  simp only [modulusOffsets,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors,
    Finset.mem_filter,Finset.mem_range,ProgressionSmallSieve.progressionHit]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro p
  apply forall_congr'
  intro _hp
  rw [← Nat.cast_mul,← Nat.cast_add,Int.natCast_modEq_iff]
  rfl

theorem large_modulus_coprime_small (w : ℝ) (d : ℕ) (hd : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors,w < (p : ℝ)) (p : ℕ) (hp : p.Prime) (hpw : (p : ℝ) ≤ w) :
    d.Coprime p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hpd
  have h := hlarge p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hd.ne_zero⟩)
  linarith

end ErdosModulusRelative



namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean

theorem modulus_small_relative (w : ℝ) (Y d : ℕ) (a : ℕ → ℕ)
    (hw : 2 ≤ w) (hY : 0 < Y) (hd : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors,w < (p : ℝ))
    (hv : 960048 ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w) :
    |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
      (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤
        3*Real.exp (-(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w)/192) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hb := primeHitRepresentative_spec d hd a
  have hJ : 0 < (Y : ℝ)/(d : ℝ) := by positivity
  have hN := hitLength_error Y d (primeHitRepresentative d hd a) hd0 hb.1 hb.2.1
  have hs := ProgressionSmallSieve.progression_small_relative
    (hitLength Y d (primeHitRepresentative d hd a)) w ((Y : ℝ)/(d : ℝ))
    (primeHitRepresentative d hd a : ℤ) d a hw hJ hN hv
    (large_modulus_coprime_small w d hd hlarge)
  rw [modulus_count_eq_offsets Y _ a d hd,offsets_eq_progression,Int.cast_natCast]
  exact hs

theorem uniform_modulus_small_relative (eps : ℝ) (heps : 0 < eps) :
    ∃ K0 w0 : ℝ,1 ≤ K0 ∧ 1 < w0 ∧ ∀ w : ℝ,w0 ≤ w →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → 0 < d → Squarefree d →
        (∀ p ∈ d.primeFactors,w < (p : ℝ)) →
        K0 ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w →
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
          (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤ eps := by
  let K0 := max (960048 : ℝ) (-192*Real.log (eps/3))
  have hK : 960048 ≤ K0 := le_max_left _ _
  have hKe : -192*Real.log (eps/3) ≤ K0 := le_max_right _ _
  have hExp : 3*Real.exp (-K0/192) ≤ eps := by
    have hh : -K0/192 ≤ Real.log (eps/3) := by linarith
    have he := Real.exp_le_exp.mpr hh
    rw [Real.exp_log (by positivity : 0 < eps/3)] at he
    linarith
  refine ⟨K0,2,by linarith,by norm_num,?_⟩
  intro w hw Y d a hY _hdpos hd hlarge hv
  calc
    _ ≤ 3*Real.exp (-(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w)/192) :=
      modulus_small_relative w Y d a hw hY hd hlarge (hK.trans hv)
    _ ≤ 3*Real.exp (-K0/192) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ _ := hExp

end ErdosModulusRelative



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
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
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

end NumberTheoryLean.CandidateTerminalGeometry



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



namespace NumberTheoryLean.SingletonBinSelection
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SortedLabelRepetition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SortedLabelRepetition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord


theorem source_word_labels_ordered {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hd : ps.Pairwise (· > ·)) (hsrc : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  apply hd.imp_of_mem
  intro p q hp hq hpq
  exact global_label_mono hw htop hxi (hsrc p hp) (hsrc q hq) hpq.le

end NumberTheoryLean.SortedLabelRepetition


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepeatedPositionNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPositionNeighbors


theorem repeated_position_neighbor {α : Type*} {n : ℕ} (f : α → Fin n)
    (pre tail : List α) (p : α)
    (hord : ((pre++p::tail).map f).Pairwise (· ≥ ·))
    (hcount : 2 ≤ ((pre++p::tail).map f).count (f p)) :
    (∃ pre' q,pre=pre'++[q] ∧ f q=f p) ∨ (∃ q tail',tail=q::tail' ∧ f q=f p) := by
  have ho : (pre.map f).Pairwise (· ≥ ·) ∧ ((p::tail).map f).Pairwise (· ≥ ·) ∧
      ∀ a ∈ pre.map f,∀ b ∈ (p::tail).map f,a ≥ b := by
    simpa only [List.map_append,List.pairwise_append] using hord
  by_cases hm : f p ∈ pre.map f
  · have hn : pre ≠ [] := by intro he; simp [he] at hm
    let q := pre.getLast hn
    have hqmem : f q ∈ pre.map f := List.mem_map.mpr ⟨q,List.getLast_mem hn,rfl⟩
    have hqge : f p ≤ f q := ho.2.2 _ hqmem _ (by simp)
    have hqle : f q ≤ f p := by
      have hh := ho.1.rel_getLast hm
      simpa only [List.getLast_map] using hh
    exact Or.inl ⟨pre.dropLast,q,(List.dropLast_append_getLast hn).symm,le_antisymm hqle hqge⟩
  · have hc : 0 < (tail.map f).count (f p) := by
      have hz : (pre.map f).count (f p)=0 := List.count_eq_zero.mpr hm
      simpa [List.map_append,List.count_append,hz] using hcount
    have ht := List.count_pos_iff.mp hc
    cases tail with
    | nil => simp at ht
    | cons q tail =>
      have hqle : f q ≤ f p := (List.pairwise_cons.mp ho.2.1).1 _ (by simp)
      have htail : ((q::tail).map f).Pairwise (· ≥ ·) := (List.pairwise_cons.mp ho.2.1).2
      have hqge : f p ≤ f q := by
        have hh := htail.rel_head ht
        simpa using hh
      exact Or.inr ⟨q,tail,rfl,le_antisymm hqle hqge⟩
end NumberTheoryLean.RepeatedPositionNeighbors


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RepeatedWordData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedWordData
open _root_.Set FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry ActualPrimeHigh
open CandidateTerminalGeometry MarkedPrefixTools
open RepeatedPairEvents RepeatedPairProbability ActualSourceTags PrimeBinRepresentatives
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


variable {w ell S : ℝ} {start : Node}

theorem history_last_mem (h : History w ell S start) (hne : h.primes ≠ []) : h.primes.getLastD 0 ∈ h.primes := by
  have he : h.primes.getLastD 0=h.primes.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  exact List.getLast_mem hne

theorem history_nonempty_cutoff_gt (hw : 1 < w) (h : History w ell S start) (hne : h.primes ≠ []) :
    ell < h.node.cutoff := by
  have hh := (allowed_prime_bounds hw h.admissible _ (history_last_mem h hne)).2.1
  rwa [← terminal_lastD w start h.primes hne] at hh

end NumberTheoryLean.RepeatedWordData


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SourceCompactSingletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CompactPositionRepetition
open FinitePathGeometry PrimeHistories RepeatedWordEvents RepeatedPositionNeighbors
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem compact_position_repetition {n : ℕ} (lab : ℕ → Fin n) (w L : ℝ) (z : Node)
    (pre tail : List ℕ) (p : ℕ)
    (hord : ((pre++p::tail).map lab).Pairwise (· ≥ ·))
    (hc : 2 ≤ ((pre++p::tail).map lab).count (lab p))
    (hgap : (terminal w z pre).gap ≤ L) (hp : 0 ≤ primeExponent w p) :
    compactAdjacentWord w lab L z (pre++p::tail) := by
  rcases repeated_position_neighbor lab pre tail p hord hc with ⟨pre',q,hpre,hq⟩ | ⟨q,tail',htail,hq⟩
  · refine ⟨pre',q,p,tail,?_,hq,?_⟩
    · rw [hpre]
      simp
    · rwa [← hpre]
  · refine ⟨pre,p,q,tail',by rw [htail],hq.symm,?_⟩
    have hg : (terminal w z (pre++[p])).gap=(terminal w z pre).gap-primeExponent w p := by
      simp [terminal,step]
    rw [hg]
    linarith

theorem compact_position_singleton {n : ℕ} (lab : ℕ → Fin n) (w L : ℝ) (z : Node)
    (ps : List ℕ) (hord : (ps.map lab).Pairwise (· ≥ ·))
    (hno : ¬compactAdjacentWord w lab L z ps)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail)
    (hgap : (terminal w z pre).gap ≤ L) (hp : 0 ≤ primeExponent w p) :
    (ps.map lab).count (lab p) ≤ 1 := by
  by_contra hc
  have hc' : 2 ≤ (ps.map lab).count (lab p) := by omega
  apply hno
  rw [he] at hord hc' ⊢
  exact compact_position_repetition lab w L z pre tail p hord hc' hgap hp
end NumberTheoryLean.CompactPositionRepetition



namespace NumberTheoryLean.SourceCompactSingletons
open FinitePathGeometry PrimeHistories RepeatedWordEvents CompactPositionRepetition SortedLabelRepetition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem source_compact_singleton {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (L : ℝ) (z : Node) (ps : List ℕ) (hd : ps.Pairwise (· > ·))
    (hsrc : ∀ p ∈ ps,p ∈ sourcePrimeSet w top)
    (hno : ¬compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail) (hgap : (terminal w z pre).gap ≤ L) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p)=1 := by
  have hp : p ∈ ps := by rw [he]; simp
  have hp' := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsrc p hp)
  have hxp : 0 ≤ primeExponent w p := by
    unfold primeExponent
    exact div_nonneg (Real.log_nonneg (le_trans hw.le hp'.2.1.le)) (Real.log_nonneg hw.le)
  have hle := compact_position_singleton _ w L z ps
    (source_word_labels_ordered hw htop hxi ps hd hsrc) hno pre tail p he hgap hxp
  have hpos : 0 < (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p) :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  omega

end NumberTheoryLean.SourceCompactSingletons


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

end NumberTheoryLean.ActualRegularBoxes



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

end NumberTheoryLean.ActualRegularAdmission


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceFirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FirstGapCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ErdosSearchCount
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem first_gap_crossing {w ell S : ℝ} (hell : 0 ≤ ell) (z : Node)
    (hs : Valid z.side z.ratio) (ps : List ℕ) (ha : allowed w ell S z ps)
    (H : ℝ) (hstart : H < z.gap) (hend : (terminal w z ps).gap ≤ H) :
    ∃ pre p tail,ps=pre++p::tail ∧ H < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ H ∧ H/3 < (terminal w z (pre++[p])).gap := by
  induction ps generalizing z with
  | nil => exact False.elim (not_lt_of_ge hend hstart)
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (allowed_cons w ell S z p ps).mp ha
    by_cases hc : (step w z p).gap ≤ H
    · have hh := child_gap_third hell hs hp
      exact ⟨[],p,ps,rfl,hstart,hc,by change H/3 < (step w z p).gap; linarith⟩
    · obtain ⟨pre,q,tail,he,hpre,hend,hlo⟩ := ih (step w z p) (child_valid hs hp) ht (lt_of_not_ge hc) hend
      refine ⟨p::pre,q,tail,by rw [List.cons_append,he],hpre,?_,?_⟩
      · simpa only [List.cons_append,terminal_cons] using hend
      · simpa only [List.cons_append,terminal_cons] using hlo
end NumberTheoryLean.FirstGapCrossing



namespace NumberTheoryLean.SourceFirstCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership FirstGapCrossing
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem source_first_above {w ell S B theta : ℝ} (hB : 0 < B) (htheta : theta ≤ 1/2)
    (z : Node) (hs : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    {p : ℕ} (hp : p ∈ nodeChildren w ell S z) : theta*B < (step w z p).gap := by
  have hcap := (Finset.mem_filter.mp hp).2.2.1
  have hx : primeExponent w p ≤ B := by
    change capGuard z.closed z.cutoff (primeExponent w p) at hcap
    rw [hcut] at hcap
    cases h : z.closed <;> simp [capGuard,h] at hcap
    · exact hcap.le
    · exact hcap
  have hgap : z.gap=z.ratio*B := by
    have he : B=z.gap/z.ratio := hcut.symm.trans hc
    have hh := (eq_div_iff (by linarith : z.ratio ≠ 0)).mp he
    nlinarith
  change theta*B < z.gap-primeExponent w p
  rw [hgap]
  nlinarith

theorem source_gap_crossing {w ell S B theta : ℝ} (hell : 0 ≤ ell) (hB : 0 < B)
    (htheta : theta ≤ 1/2) (z : Node) (hs : Valid z.side z.ratio)
    (h199 : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    (ps : List ℕ) (ha : allowed w ell S z ps) (hend : (terminal w z ps).gap ≤ theta*B) :
    ∃ pre p tail,pre ≠ [] ∧ ps=pre++p::tail ∧ theta*B < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ theta*B ∧ theta*B/3 < (terminal w z (pre++[p])).gap := by
  have hg : z.gap=z.ratio*B := (SourceNodeCoordinates.node_gap_eq hs hc hcut).trans (mul_comm _ _)
  have hstart : theta*B < z.gap := by rw [hg]; nlinarith
  obtain ⟨pre,p,tail,he,hpre,hhi,hlo⟩ := first_gap_crossing hell z hs ps ha (theta*B) hstart hend
  refine ⟨pre,p,tail,?_,he,hpre,hhi,hlo⟩
  intro hn
  subst pre
  simp only [List.nil_append] at he hhi
  have hp := ((allowed_cons w ell S z p tail).mp (he ▸ ha)).1
  exact (not_lt_of_ge hhi) (source_first_above hB htheta z h199 hc hcut hp)
end NumberTheoryLean.SourceFirstCrossing


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
open SourceCompactSingletons IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem geometric_compact_singleton {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail) (hgap : (terminal w z pre).gap ≤ L) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p)=1 := by
  have hr := Finset.mem_filter.mp hp
  have hd := ErdosPrimeInputs.PrimePrefixMass.mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr.1).1
  exact source_compact_singleton hw htop hxi L z ps hd.1 hd.2 hr.2.1 pre tail p he hgap
end NumberTheoryLean.GeometricRegularWords


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

theorem above_word_product {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) :
    (descendingWord (aboveSelection f j)).prod=selectionProduct (aboveSelection f j) := by
  apply descendingWord_product (globalBins w top xi)
    (fun i k hik => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i k hik)
  intro k
  exact ((mem_selections _ _ _).mp (above_selection_mem _ m f hf j) k).1
end NumberTheoryLean.BinCutPrefixGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_SourcePrimeProductData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourcePrimeProductData
open FinitePathGeometry PrimeHistories ReferenceAdmission LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

theorem source_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (ps : List ℕ)
    (hd : ps.Pairwise (· > ·)) (hp : ∀ p∈ps,p ∈ sourcePrimeSet w top) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  have hn : ps.Nodup := hd.imp (fun h => ne_of_gt h)
  have hprime : ∀ p∈ps,p.Prime := fun p h => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p h)).1
  have hpos : 0 < ps.prod := List.prod_pos (fun p h => (hprime p h).pos)
  have he : (∏ p∈ps.toFinset,p)=ps.prod := by simpa using List.prod_toFinset (fun p : ℕ => p) hn
  have hprimeF : ∀ p∈ps.toFinset,p.Prime := fun p h => hprime p (List.mem_toFinset.mp h)
  have hsq : Squarefree (∏ p∈ps.toFinset,p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpp q hqq hpq
      simp only [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprimeF p hpp) (hprimeF q hqq)).mpr hpq
    · intro p hpp
      exact (hprimeF p hpp).squarefree
  have hfac : ps.prod.primeFactors=ps.toFinset := by
    rw [← he]
    exact ErdosInverseCounts.primeFactors_product ps.toFinset hprimeF
  refine ⟨hpos,by rwa [he] at hsq,?_⟩
  intro p hpf
  rw [hfac] at hpf
  exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p (List.mem_toFinset.mp hpf))).2.1

theorem reference_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (i : Side) (r : ℝ) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) i r) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  classical
  have hh := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  exact source_word_product_data hw htop ps hh.1 hh.2
end NumberTheoryLean.SourcePrimeProductData


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_WordIntervalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WordIntervalGeometry
open FinitePathGeometry PrimeHistories PrimeProductLogCoordinates RepresentativeAdmission
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem word_interval_gap {w a : ℝ} (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2) (ps : List ℕ) (hp : ∀ p∈ps,0 < p) :
    wordIntervalExponent w Y ps=(terminal w z ps).gap+a-2 := by
  have hh := terminal_gap_log_quotient Y hY z hroot ps hp
  unfold wordIntervalExponent
  linarith

theorem gap_prefix_mono (w : ℝ) (z : Node) (pre tail : List ℕ)
    (hp : ∀ p∈tail,0 ≤ primeExponent w p) :
    (terminal w z (pre++tail)).gap ≤ (terminal w z pre).gap := by
  rw [terminal_append,terminal_gap_sum]
  have hh : 0 ≤ (tail.map (primeExponent w)).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact hp p hp')
  linarith

theorem interval_exponent_step (w : ℝ) (Y : ℕ) (hY : 0 < Y) (pre : List ℕ) (u : ℕ)
    (hp : 0 < pre.prod) (hu : 0 < u) :
    wordIntervalExponent w Y (pre++[u])=wordIntervalExponent w Y pre-primeExponent w u := by
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpr : (pre.prod:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hur : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold wordIntervalExponent primeExponent
  rw [List.prod_append,List.prod_singleton,Nat.cast_mul,Real.log_div hYr (mul_ne_zero hpr hur),
    Real.log_div hYr hpr,Real.log_mul hpr hur]
  ring
end NumberTheoryLean.WordIntervalGeometry


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


namespace NumberTheoryLean.FiniteErrorTelescoping


theorem endpoint_difference_le (E : List ℕ → ℝ) (pre ps : List ℕ) (delta : ℝ)
    (h : ∀ before p after,ps=before++p::after →
      |E ((pre++before)++[p])-E (pre++before)| ≤ delta) :
    |E (pre++ps)-E pre| ≤ (ps.length:ℝ)*delta := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
    have hfirst := h [] p ps rfl
    simp only [List.append_nil] at hfirst
    have htail : ∀ before q after,ps=before++q::after →
        |E (((pre++[p])++before)++[q])-E ((pre++[p])++before)| ≤ delta := by
      intro before q after he
      have hh := h (p::before) q after (by rw [List.cons_append,he])
      simpa only [List.append_assoc,List.singleton_append] using hh
    have hh := ih (pre++[p]) htail
    have htri := abs_add_le (E ((pre++[p])++ps)-E (pre++[p])) (E (pre++[p])-E pre)
    have he : (pre++[p])++ps=pre++p::ps := by simp
    rw [he] at hh htri
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    have htel : E (pre++p::ps)-E (pre++[p])+(E (pre++[p])-E pre)=E (pre++p::ps)-E pre := by ring
    rw [htel] at htri
    nlinarith

theorem exists_large_edge (E : List ℕ → ℝ) (pre ps : List ℕ) (delta : ℝ)
    (h : (ps.length:ℝ)*delta < |E (pre++ps)-E pre|) :
    ∃ before p after,ps=before++p::after ∧ delta < |E ((pre++before)++[p])-E (pre++before)| := by
  by_contra! hn
  have hh := endpoint_difference_le E pre ps delta hn
  linarith

theorem witness_from_endpoints (E : List ℕ → ℝ) (pre ps : List ℕ) (H : ℕ) (hH : 0 < H)
    (eps : ℝ) (heps : 0 < eps) (hlen : ps.length ≤ H)
    (hstart : |E pre| ≤ eps/2) (hend : eps < |E (pre++ps)|) :
    ∃ before p after,ps=before++p::after ∧ eps/(4*H) < |E ((pre++before)++[p])-E (pre++before)| := by
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hdelta : 0 ≤ eps/(4*H) := by positivity
  have hm : (ps.length:ℝ)*(eps/(4*H)) ≤ eps/4 := by
    have hl : (ps.length:ℝ) ≤ H := by exact_mod_cast hlen
    have hh := mul_le_mul_of_nonneg_right hl hdelta
    have he : (H:ℝ)*(eps/(4*H))=eps/4 := by field_simp [hHr.ne']
    rwa [he] at hh
  have htri := abs_add_le (E (pre++ps)-E pre) (E pre)
  simp only [sub_add_cancel] at htri
  apply exists_large_edge E pre ps (eps/(4*H))
  linarith
end NumberTheoryLean.FiniteErrorTelescoping



namespace NumberTheoryLean.ActualCountErrorEdges
open ErdosInverseCounts


theorem relative_error_increment (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    relativeCountError Y small a V0 (d*u)-relativeCountError Y small a V0 d=
      ((modulusCount Y small a (d*u):ℝ)-(modulusCount Y small a d:ℝ)/(u:ℝ))/
        ((Y:ℝ)*V0/((d:ℝ)*(u:ℝ))) := by
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hdr : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hur : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold relativeCountError
  rw [Nat.cast_mul]
  field_simp [hYr,hdr,hur,hV.ne']
  ring

theorem relative_large_edge_iff (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 delta : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    delta < |relativeCountError Y small a V0 (d*u)-relativeCountError Y small a V0 d| ↔
      NodeBadEdge Y small a delta V0 d u := by
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have hur : 0 < (u:ℝ) := by exact_mod_cast hu
  have hmu : 0 < (Y:ℝ)*V0/((d:ℝ)*(u:ℝ)) := by positivity
  rw [relative_error_increment Y small a V0 hY hV d u hd hu,abs_div,abs_of_pos hmu]
  rw [lt_div_iff₀ hmu]
  unfold NodeBadEdge
  simp only [mul_div_assoc,mul_assoc]

theorem word_large_edge_iff (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 delta : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (pre : List ℕ) (u : ℕ) (hd : 0 < pre.prod) (hu : 0 < u) :
    delta < |wordCountError Y small a V0 (pre++[u])-wordCountError Y small a V0 pre| ↔
      NodeBadEdge Y small a delta V0 pre.prod u := by
  unfold wordCountError
  rw [List.prod_append,List.prod_singleton]
  exact relative_large_edge_iff Y small a V0 delta hY hV pre.prod u hd hu
end NumberTheoryLean.ActualCountErrorEdges



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

end NumberTheoryLean.BoundedEdgeBins


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_LatePrimeRatio
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LatePrimeRatio
open FinitePathGeometry PrimeHistories PrimeTiltGeometry RepeatedWordData

attribute [local instance] Classical.propDecidable

theorem child_ratio_min {w ell S : ℝ} (z : Node) {p : ℕ} (hp : p ∈ nodeChildren w ell S z) :
    minRatio z.side z.ratio ≤ (step w z p).ratio := (Finset.mem_filter.mp hp).2.2.2.1

theorem two_step_ratio_one {w ell S : ℝ} (z : Node) {p q : ℕ}
    (hp : p ∈ nodeChildren w ell S z) (hq : q ∈ nodeChildren w ell S (step w z p)) :
    1 ≤ (step w (step w z p) q).ratio := by
  have h1 := child_ratio_min z hp
  have h2 := child_ratio_min (step w z p) hq
  cases hi : z.side with
  | even =>
    have hside : (step w z p).side=.odd := by simp [step,hi,Side.flip]
    rw [hside] at h2
    exact (by norm_num : (1:ℝ)≤2).trans ((le_max_left _ _).trans h2)
  | odd =>
    rw [hi] at h1
    have hfirst : 2 ≤ (step w z p).ratio := (le_max_left _ _).trans h1
    have hside : (step w z p).side=.even := by simp [step,hi,Side.flip]
    rw [hside] at h2
    change (step w z p).ratio-1 ≤ (step w (step w z p) q).ratio at h2
    linarith

theorem allowed_late_ratio_one {w ell S : ℝ} (z : Node) (ps : List ℕ)
    (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) : 1 ≤ (terminal w z ps).ratio := by
  induction ps generalizing z with
  | nil => simp at hlen
  | cons p ps ih =>
    obtain ⟨hhead,hrest⟩ := (allowed_cons w ell S z p ps).mp hp
    cases ps with
    | nil => simp at hlen
    | cons q qs =>
      cases qs with
      | nil =>
        have hq := ((allowed_cons w ell S (step w z p) q []).mp hrest).1
        exact two_step_ratio_one z hhead hq
      | cons r rs => exact ih (step w z p) hrest (by simp)

theorem allowed_late_gap_cutoff {w ell S : ℝ} (hw : 1 < w) (hell : 1 ≤ ell)
    (z : Node) (ps : List ℕ) (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) :
    (terminal w z ps).cutoff ≤ (terminal w z ps).gap := by
  have hne : ps ≠ [] := by intro he; simp [he] at hlen
  let h : History w ell S z := ⟨ps,hp⟩
  have hx := history_nonempty_cutoff_gt hw h hne
  have hx0 : 0 < (terminal w z ps).cutoff := by change ell < (terminal w z ps).cutoff at hx; linarith
  have hr := allowed_late_ratio_one z ps hp hlen
  have he := CandidateTerminalGeometry.terminal_ratio_div_cutoff w z ps hne hx0.ne'
  rw [he] at hr
  exact (one_le_div hx0).mp hr
end NumberTheoryLean.LatePrimeRatio


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

end NumberTheoryLean.BoundedEdgeSuffixRank



namespace NumberTheoryLean.RecentReferenceSegment
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh
open SourceFirstCrossing WordIntervalGeometry LatePrimeRatio BoundedEdgeSuffixRank ActualReferencePrefixes
open LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem recent_reference_segment {w top B K Kstar a : ℝ} (hw : 1 < w) (htop : w < top)
    (hK : 3 ≤ K) (hKstar : K+10 ≤ Kstar) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hB3 : 3 ≤ B) (hBlarge : 2*(Kstar+2-a) ≤ B)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B)
    (hclosed : z.closed=true) (hpower : w^B=top) (ps : List ℕ)
    (hps : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hend : (terminal w z ps).gap ≤ K) :
    ∃ pre rest : List ℕ,ps=pre++rest ∧ pre ≠ [] ∧ rest ≠ [] ∧
      Kstar < wordIntervalExponent w Y pre ∧ rest.length ≤ ⌈2*Kstar+10⌉₊ ∧
      ∀ before u after,rest=before++u::after →
        wordIntervalExponent w Y (pre++before) ≤ 2*Kstar+3 ∧
        a ≤ wordIntervalExponent w Y ((pre++before)++[u]) ∧
        primeExponent w u ≤ 2*Kstar+3 ∧ (terminal w z (pre++before)).gap ≤ 2*Kstar+5 := by
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hu := (source_reference_transport hw htop z hs hz hg hclosed hcap ps hps).1
  have hua := (mem_uncappedPrefixes hw z ps).mp hu
  obtain ⟨S,_hS,ha⟩ := (uncapped_iff_exists_ceiling w 1 z ps).mp hua
  have hBp : 0 < B := by linarith
  let H := Kstar+2-a
  have hH : 0 < H := by dsimp [H] <;> linarith
  have htheta : H/B ≤ 1/2 := by apply (div_le_iff₀ hBp).mpr; dsimp [H] <;> linarith
  have hthetaB : (H/B)*B=H := div_mul_cancel₀ H hBp.ne'
  have he : (terminal w z ps).gap ≤ (H/B)*B := by rw [hthetaB]; dsimp [H] <;> linarith
  obtain ⟨pre,p,tail,hpre,hword,_hbefore,hcross,_hlo⟩ :=
    source_gap_crossing (by norm_num) hBp htheta z hs h199 hz hcut ps ha he
  rw [hthetaB] at hcross _hbefore
  have hword' : ps=(pre++[p])++tail := by simpa only [List.append_assoc,List.singleton_append] using hword
  have hac : allowed w 1 S z (pre++[p]) := ((allowed_append w 1 S z (pre++[p]) tail).mp (hword' ▸ ha)).1
  have hlen : 2 ≤ (pre++[p]).length := by have hh := List.length_pos_iff.mpr hpre; simp only [List.length_append,List.length_singleton]; omega
  have hlate := allowed_late_gap_cutoff hw (by norm_num : (1:ℝ)≤1) z (pre++[p]) hac hlen
  have hxc : (terminal w z (pre++[p])).cutoff=primeExponent w p := by simp [terminal,step]
  have hrc : (terminal w z (pre++[p])).gap=(terminal w z pre).gap-primeExponent w p := by simp [terminal,step]
  rw [hxc] at hlate
  have hpreGap : (terminal w z pre).gap ≤ 2*H := by linarith
  have hsrc := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1).2
  have hpos : ∀ q∈ps,0 < q := fun q hq => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (hsrc q hq)).1.pos
  have hexp : ∀ q∈ps,1 ≤ primeExponent w q := by
    intro q hq
    have hqw := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (hsrc q hq)
    exact ((one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hqw.2.1)).le
  have hpreSub : pre ⊆ ps := by intro q hq; rw [hword]; exact List.mem_append_left _ hq
  have hrestSub : p::tail ⊆ ps := by intro q hq; rw [hword]; exact List.mem_append_right _ hq
  have hvpre := word_interval_gap Y hY z hroot pre (fun q hq => hpos q (hpreSub hq))
  have hVpre : wordIntervalExponent w Y pre ≤ 2*Kstar+3 := by dsimp [H] at hpreGap <;> linarith
  have hhigh : Kstar < wordIntervalExponent w Y pre := by dsimp [H] at _hbefore <;> linarith
  have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap ps hps).2
  have hsum := list_length_le_exponents w (p::tail) (fun q hq => hexp q (hrestSub hq))
  have hfinalGap : (terminal w z ps).gap=(terminal w z pre).gap-((p::tail).map (primeExponent w)).sum := by
    rw [hword,terminal_append]
    exact RepresentativeAdmission.terminal_gap_sum w _ _
  have hrestLength : (p::tail).length ≤ ⌈2*Kstar+10⌉₊ := by
    have hh : ((p::tail).length:ℝ) ≤ 2*Kstar+10 := by linarith
    exact_mod_cast hh.trans (Nat.le_ceil (2*Kstar+10))
  refine ⟨pre,p::tail,hword,hpre,by simp,hhigh,hrestLength,?_⟩
  intro before u after hrest
  have hparword : ps=(pre++before)++u::after := by rw [hword,hrest,List.append_assoc]
  have hchildword : ps=((pre++before)++[u])++after := by simpa only [List.append_assoc,List.singleton_append] using hparword
  have hparSub : pre++before ⊆ ps := by intro q hq; rw [hparword]; exact List.mem_append_left _ hq
  have hchildSub : (pre++before)++[u] ⊆ ps := by intro q hq; rw [hchildword]; exact List.mem_append_left _ hq
  have hbeforeSub : before ⊆ ps := fun q hq => hparSub (List.mem_append_right _ hq)
  have hmono := gap_prefix_mono w z pre before (fun q hq => (hexp q (hbeforeSub hq)).trans' (by norm_num))
  have hvpar := word_interval_gap Y hY z hroot (pre++before) (fun q hq => hpos q (hparSub hq))
  have hvchild := word_interval_gap Y hY z hroot ((pre++before)++[u]) (fun q hq => hpos q (hchildSub hq))
  have hchildin : (pre++before)++[u] ∈ ps.inits := (List.mem_inits _ _).mpr ⟨after,hchildword.symm⟩
  have hchildfloor := reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap ps _ hps hchildin
  have huMem : u ∈ ps := by rw [hparword]; simp
  have hstep := interval_exponent_step w Y hY (pre++before) u
    (List.prod_pos (fun q hq => hpos q (hparSub hq))) (hpos u huMem)
  refine ⟨?_,?_,?_,?_⟩ <;> linarith
end NumberTheoryLean.RecentReferenceSegment



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GeometricEdgeWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricEdgeWitness
open PrimeHistories GeometricRegularWords SourceCompactSingletons ActualWordSelection
open ErdosCofactorChoices ErdosSubsetWord BoundedCandidateCount BoundedEdgeBins FullBoxLengthBounds
open BinCutSelections BinCutPrefixGeometry SelectionWordSplit
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem decreasing_edge_prefix_unique (ps pre tail pre' tail' : List ℕ) (u : ℕ)
    (hd : ps.Pairwise (· > ·)) (he : ps=pre++u::tail) (he' : ps=pre'++u::tail') : pre=pre' := by
  have hno : u ∉ pre := by
    intro hu
    have hh := hd
    rw [he,List.pairwise_append] at hh
    exact (lt_irrefl u) (hh.2.2 u hu u (by simp))
  have hno' : u ∉ pre' := by
    intro hu
    have hh := hd
    rw [he',List.pairwise_append] at hh
    exact (lt_irrefl u) (hh.2.2 u hu u (by simp))
  have hidx : ps.idxOf u=pre.length := by rw [he,List.idxOf_append_of_notMem hno]; simp
  have hidx' : ps.idxOf u=pre'.length := by rw [he',List.idxOf_append_of_notMem hno']; simp
  have hlen : pre.length=pre'.length := hidx.symm.trans hidx'
  calc
    pre=ps.take pre.length := by rw [he]; simp
    _=ps.take pre'.length := by rw [hlen]
    _=pre' := by rw [he']; simp

theorem geometric_word_bounded_edge {w top xi C B R L alpha beta M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Y : ℕ) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z)
    (pre tail : List ℕ) (u : ℕ) (he : ps=pre++u::tail)
    (hgap : (terminal w z pre).gap ≤ L)
    (hM : Real.log ((Y:ℝ)/(pre.prod:ℝ))/Real.log w ≤ M) (hX : primeExponent w u ≤ X) :
    boundedEdgeBin w top xi Y (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) M X
      (label (zero_lt_one.trans hw) htop hxi u) := by
  have hreg := (Finset.mem_filter.mp hp).1
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hreg).1
  have hn : ps.Nodup := hd.1.imp (fun h => ne_of_gt h)
  let lab := label (zero_lt_one.trans hw) htop hxi
  let m := wordMultiplicity lab ps
  let f := wordSelection lab ps
  let j := lab u
  have hf : f ∈ selections (globalBins w top xi) m := wordSelection_mem hw htop hxi ps hd.2
  have hsingle := GeometricRegularWords.geometric_compact_singleton hw htop hxi z ps hp pre tail u he hgap
  have hcard : (f j).card=1 := (wordMultiplicity_count lab ps hn j).trans hsingle
  have hu : u ∈ f j := by
    change u ∈ ps.toFinset.filter (fun p => lab p=j)
    simp [he,j]
  obtain ⟨v,hfv⟩ := Finset.card_eq_one.mp hcard
  have huv : u=v := by simpa only [hfv,Finset.mem_singleton] using hu
  have hfu : f j={u} := by rwa [← huv] at hfv
  have hword := wordSelection_recovers lab ps hd.1
  have hsplit := selected_word_split hw htop hxi m f hf j u hfu
  rw [hword] at hsplit
  have hpre := decreasing_edge_prefix_unique ps pre tail (descendingWord (aboveSelection f j))
    (descendingWord (belowSelection f j)) u hd.1 he hsplit
  refine ⟨f,hf,u,hfu,?_,hX⟩
  unfold parentLength
  rw [← above_word_product hw htop hxi m f hf j,← hpre]
  exact hM
end NumberTheoryLean.GeometricEdgeWitness


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ParentProductReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentProductReadout
open ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection SingletonBinProduct TwoPrimeObservableSum ParentTailPartition
open PrimeHistories BinCutSelections BinCutPrefixGeometry SelectionWordSplit GeometricEdgeWitness
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem parent_product_readout {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (i j : Fin n) (hji : j < i) (hi : m i=1) :
    selectionProduct (aboveSelection f j)=pickedPrime f i*selectionProduct (parentCofactorSelection f i j) := by
  obtain ⟨p,_hp,hfi,_⟩ := singleton_selection_recovery P m i hi f hf
  have hA : aboveSelection f j i={p} := by simp [aboveSelection,hji,hfi]
  have hpick : pickedPrime f i=p := by simp [pickedPrime,hfi]
  have he : eraseSelection (aboveSelection f j) i i=∅ := by simp [eraseSelection]
  have hh := filled_product (eraseSelection (aboveSelection f j) i) i p he
  rw [fill_erase (aboveSelection f j) i p hA,← hpick] at hh
  exact hh

theorem actual_prefix_product_readout {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (pre tail : List ℕ) (u : ℕ) (he : descendingWord f=pre++u::tail) (hfu : f j={u}) :
    pre.prod=pickedPrime f i*selectionProduct (parentCofactorSelection f i j) ∧ pickedPrime f j=u := by
  have hsplit := selected_word_split hw htop hxi m f hf j u hfu
  have hpre := decreasing_edge_prefix_unique (descendingWord f) pre tail (descendingWord (aboveSelection f j))
    (descendingWord (belowSelection f j)) u (descendingWord_strict f) he hsplit
  refine ⟨?_,by simp [pickedPrime,hfu]⟩
  rw [hpre,above_word_product hw htop hxi m f hf j]
  exact parent_product_readout (globalBins w top xi) m f hf i j hji hi
end NumberTheoryLean.ParentProductReadout


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


namespace NumberTheoryLean.RecentCountWitness
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission ActualReferencePrefixes
open WordIntervalGeometry RecentReferenceSegment ActualCountErrorEdges FiniteErrorTelescoping SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts ErdosModulusRelative
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem recent_count_witness (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B₀ w₀ : ℝ,K+10 < Kstar ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ _hw : 1 < w,∀ _htop : w < top,
      ∀ aStar : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 → z.side=.even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ ps : List ℕ,
      ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (terminal w z ps).gap ≤ K →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| →
      ∃ before u after,ps=before++u::after ∧ (u::after).length ≤ ⌈2*Kstar+10⌉₊ ∧
        NodeBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊:ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊) before.prod u ∧
        wordIntervalExponent w Y before ≤ 2*Kstar+3 ∧ aStar ≤ wordIntervalExponent w Y (before++[u]) ∧
        primeExponent w u ≤ 2*Kstar+3 ∧ (terminal w z before).gap ≤ 2*Kstar+5 := by
  obtain ⟨K0,W,hK0,hW,hSmall⟩ := uniform_modulus_small_relative (eps/2) (by positivity)
  let Kstar := max (K+11) K0
  have hKstar : K+10 < Kstar := (by linarith : K+10<K+11).trans_le (le_max_left _ _)
  have hK0star : K0 ≤ Kstar := le_max_right _ _
  refine ⟨Kstar,max 3 (2*(Kstar+2)),max W 2,hKstar,le_max_left _ _,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop aStar ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hps hend hbad
  have hB3 : 3 ≤ B := (le_max_left _ _).trans hB
  have hBlarge : 2*(Kstar+2-aStar) ≤ B := by
    have hh := (le_max_right _ _).trans hB
    linarith
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  obtain ⟨pre,rest,hword,_hpre,_hrest,hhigh,hlen,hsegment⟩ := recent_reference_segment hw htop hK hKstar.le
    ha0 ha1 hB3 hBlarge Y hY z hroot hi h199 hz hcut hclosed hpower ps hps hend
  have hpreIn : pre ∈ ps.inits := (List.mem_inits _ _).mpr ⟨rest,hword.symm⟩
  have hpreRef := reference_prefix_mem w _ _ _ ps pre hps hpreIn
  have hpreData := reference_word_product_data hw htop z.side z.gap pre hpreRef
  have hstart := hSmall w ((le_max_left _ _).trans hw₀) Y pre.prod residue hY hpreData.1 hpreData.2.1 hpreData.2.2
    (hK0star.trans hhigh.le)
  change |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) pre| ≤ eps/2 at hstart
  have hH : 0 < ⌈2*Kstar+10⌉₊ := by
    have hh := Nat.le_ceil (2*Kstar+10)
    by_contra! hn
    have he : ⌈2*Kstar+10⌉₊=0 := by omega
    rw [he,Nat.cast_zero] at hh
    linarith
  obtain ⟨mid,u,after,hrest,hedge⟩ := witness_from_endpoints
    (wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊))
    pre rest ⌈2*Kstar+10⌉₊ hH eps heps hlen hstart (by rwa [← hword])
  have hfull : ps=(pre++mid)++u::after := by rw [hword,hrest,List.append_assoc]
  have hbeforeIn : pre++mid ∈ ps.inits := (List.mem_inits _ _).mpr ⟨u::after,hfull.symm⟩
  have hbeforeRef := reference_prefix_mem w _ _ _ ps _ hps hbeforeIn
  have hbeforeData := reference_word_product_data hw htop z.side z.gap _ hbeforeRef
  have huMem : u ∈ ps := by rw [hfull]; simp
  have huPos : 0 < u := ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop u).mp
    ((ErdosPrimeInputs.PrimePrefixMass.mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1).2 u huMem)).1.pos
  have hEdge := (word_large_edge_iff Y _ residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (eps/(4*(⌈2*Kstar+10⌉₊:ℝ)))
    hY hV (pre++mid) u hbeforeData.1 huPos).mp hedge
  refine ⟨pre++mid,u,after,hfull,?_,hEdge,hsegment mid u after hrest⟩
  have hh : (u::after).length ≤ rest.length := by rw [hrest,List.length_append]; omega
  exact hh.trans hlen
end NumberTheoryLean.RecentCountWitness



namespace NumberTheoryLean.CountWitnessReadout
open PrimeHistories ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts
open ParentProductReadout TwoPrimeObservableSum ParentTailPartition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition


theorem selected_edge_singleton {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (j : Fin (binCount w top xi)) (hj : m j=1)
    (u : ℕ) (hu : u ∈ descendingWord f) (hlab : label (zero_lt_one.trans hw) htop hxi u=j) : f j={u} := by
  obtain ⟨k,huk⟩ := (mem_descendingWord f u).mp hu
  have hk : j=k := hlab.symm.trans (selected_prime_label hw htop hxi m f hf k huk)
  have huj : u ∈ f j := by rwa [hk]
  obtain ⟨v,hfv⟩ := Finset.card_eq_one.mp (((mem_selections _ _ _).mp hf j).2.trans hj)
  have huv : u=v := by simpa only [hfv,Finset.mem_singleton] using huj
  rwa [← huv] at hfv

theorem observed_node_bad_edge {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) m) (i j : Fin (binCount w top xi))
    (hji : j < i) (hi : m i=1) (hj : m j=1) (pre tail : List ℕ) (u : ℕ)
    (he : descendingWord f=pre++u::tail) (hlab : label (zero_lt_one.trans hw) htop hxi u=j)
    (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (hbad : NodeBadEdge Y small a delta V0 pre.prod u) :
    WitnessingBadEdge Y small a delta V0 (pickedPrime f i)
      (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  have hu : u ∈ descendingWord f := by rw [he]; simp
  have hfu := selected_edge_singleton hw htop hxi m f hf j hj u hu hlab
  have hread := actual_prefix_product_readout hw htop hxi m f hf i j hji hi pre tail u he hfu
  unfold WitnessingBadEdge
  rw [hread.2,← hread.1]
  exact hbad
end NumberTheoryLean.CountWitnessReadout



namespace NumberTheoryLean.GeometricRecentWitness
open FinitePathGeometry PrimeHistories PrimeBinMembership RecentCountWitness ActualCountErrorEdges
open GeometricRegularWords GeometricEdgeWitness ActualWordSelection ActualRegularAdmission BoundedEdgeBins
open CountWitnessReadout TwoPrimeObservableSum ParentTailPartition
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_recent_witness (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B₀ w₀ : ℝ,K+10 < Kstar ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,∀ C : ℝ,1 ≤ C → Real.log B ≤ 2*Real.log w →
      ∀ aStar alpha beta : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 → z.side=.even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ ps : List ℕ,
      ps ∈ geometricWords hw htop hxi C B K (2*Kstar+5) alpha beta z →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| →
      let m := wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps
      let f := wordSelection (label (zero_lt_one.trans hw) htop hxi) ps
      ∃ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m (2*Kstar+3) (2*Kstar+3) j ∧
        ∀ i : Fin (binCount w top xi),m i=1 → j < i →
        WitnessingBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊:ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊)
          (pickedPrime f i) (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  obtain ⟨Kstar,B₀,W,hKs,hB₀,hW,hWitness⟩ := recent_count_witness K eps hK heps
  refine ⟨Kstar,B₀,max W (Real.exp 1),hKs,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hps hbad
  have hlog : 1 ≤ Real.log w := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hw₀)
    simpa only [Real.log_exp] using hh
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hreg := (Finset.mem_filter.mp hps).1
  have hRef := regular_word_reference hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z ps hreg
  have hgap := (Finset.mem_filter.mp hreg).2.2.2.1
  obtain ⟨pre,u,tail,he,_hlen,hNode,hM,_hchild,hX,hparent⟩ := hWitness B w top hB ((le_max_left _ _).trans hw₀) hw htop
    aStar ha0 ha1 Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hRef hgap hbad
  dsimp only
  let lab := label (zero_lt_one.trans hw) htop hxi
  let m := wordMultiplicity lab ps
  let f := wordSelection lab ps
  let j := lab u
  have hCandidate := geometric_word_bounded_edge hw htop hxi Y z ps hps pre tail u he hparent hM hX
  refine ⟨j,hCandidate,?_⟩
  intro i hmi hji
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hreg).1
  have hf : f ∈ selections (globalBins w top xi) m := wordSelection_mem hw htop hxi ps hd.2
  have hword : descendingWord f=ps := wordSelection_recovers lab ps hd.1
  exact observed_node_bad_edge hw htop hxi m f hf i j hji hmi (bounded_edge_singleton m j hCandidate)
    pre tail u (hword.trans he) rfl Y _ residue _ _ hNode
end NumberTheoryLean.GeometricRecentWitness



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



namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership ActualCountErrorEdges
  GeometricRecentWitness GeometricRegularWords BoundedEdgeBins
  ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts TwoPrimeObservableSum ParentTailPartition
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem geometric_selection_recent_witness_jb247_oai (K eps : ℝ) (hK : 3 ≤ K) (heps : 0 < eps) :
    ∃ Kstar B0 w0 : ℝ,K+10 < Kstar ∧ 3 ≤ B0 ∧ 1 < w0 ∧
    ∀ (B w top : ℝ),B0 ≤ B → w0 ≤ w → ∀ (hw : 1 < w) (htop : w < top),
      ∀ (xi : ℝ) (hxi : 0 < xi) (C : ℝ),1 ≤ C → Real.log B ≤ 2*Real.log w →
      ∀ (aStar alpha beta : ℝ),0 ≤ aStar → aStar ≤ 1 → ∀ Y : ℕ,0 < Y → ∀ z : Node,
      z.gap = Real.log (Y : ℝ)/Real.log w-aStar+2 → z.side = .even → 199/100 ≤ z.ratio →
      Consistent z → z.cutoff = B → z.closed = true → w^B = top →
      ∀ (residue : ℕ → ℕ) (m : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ),
      f ∈ selections (globalBins w top xi) m →
      descendingWord f ∈ geometricWords hw htop hxi C B K (2*Kstar+5) alpha beta z →
      eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| →
      ∃ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m (2*Kstar+3) (2*Kstar+3) j ∧
        ∀ i : Fin (binCount w top xi),m i = 1 → j < i →
        WitnessingBadEdge Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
          (eps/(4*(⌈2*Kstar+10⌉₊ : ℝ))) (SmallSieveFinite.smallEuler ⌊w⌋₊)
          (pickedPrime f i) (selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) := by
  obtain ⟨Kstar,B0,w0,hKs,hB0,hw0,hcore⟩ := geometric_recent_witness K eps hK heps
  refine ⟨Kstar,B0,w0,hKs,hB0,hw0,?_⟩
  intro B w top hB hw0' hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot
    heven h199 hz hcut hclosed hpower residue m f hf hgeom hbad
  have hh := hcore B w top hB hw0' hw htop xi hxi C hC hcomp aStar alpha beta ha0 ha1 Y hY z hroot
    heven h199 hz hcut hclosed hpower residue (descendingWord f) hgeom hbad
  simpa only [SoftWitnessCapture.word_multiplicity_descending hw htop hxi m f hf,
    SoftWitnessCapture.word_selection_descending hw htop hxi m f hf] using hh

end ErdosVarianceEligible



open _root_.Filter


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceEligible.geometric_selection_recent_witness_jb247_oai := @OAI.Erdos970.ErdosVarianceEligible.geometric_selection_recent_witness_jb247_oai
