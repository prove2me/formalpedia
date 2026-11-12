-- Prove2me | solution 1 for OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:53.709706+00:00
-- url     : https://prove2.me/submissions/646ce7b3-1a39-49f1-bfa1-105fb9bcbcf7

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
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_ErdosStoppedArithmetic_moving_subbin_actual_pair_lower_jb247

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

theorem aligns_iff_modEq (a : ℕ → ℤ) (q : ℚ) (p : ℕ) :
    aligns a q p ↔ Int.ModEq (p : ℤ) ((q.den : ℤ)*a p) q.num := by
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [aligns,Int.cast_mul,Int.cast_natCast]

theorem aligned_prime_not_dvd_den (a : ℕ → ℤ) (q : ℚ) {p : ℕ}
    (hp : p.Prime) (hq : aligns a q p) : ¬p ∣ q.den := by
  intro hd
  have hd0 : (q.den : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hn0 : (q.num : ZMod p) = 0 := by
    change (q.den : ZMod p)*(a p : ZMod p) = (q.num : ZMod p) at hq
    simpa only [hd0,zero_mul] using hq.symm
  have hn : p ∣ q.num.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn0)
  have hg := Nat.dvd_gcd hn hd
  rw [q.reduced.gcd_eq_one] at hg
  exact hp.not_dvd_one hg

end ErdosInverseAlignment

end

end Erdos970

end OAI
end

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

end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseHits ErdosInverseCounts

theorem aligned_den_coprime_prime (a : ℕ → ℕ) (r : ℚ) (p : ℕ) (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) : r.den.Coprime p :=
  (hp.coprime_iff_not_dvd.mpr (aligned_prime_not_dvd_den _ r hp ha)).symm

theorem aligned_prime_hit_iff (a : ℕ → ℕ) (r : ℚ) (p t : ℕ) (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    t % p = a p % p ↔ Int.ModEq (p : ℤ) ((r.den : ℤ)*(t : ℤ)) r.num := by
  let : Fact p.Prime := ⟨hp⟩
  have hD : (r.den : ZMod p) ≠ 0 := by
    intro h
    exact aligned_prime_not_dvd_den _ r hp ha ((ZMod.natCast_eq_zero_iff _ _).mp h)
  change Nat.ModEq p t (a p) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_mul, Int.cast_natCast]
  change (t : ZMod p) = (a p : ZMod p) ↔ (r.den : ZMod p)*(t : ZMod p) = (r.num : ZMod p)
  have ha' : (r.den : ZMod p)*(a p : ZMod p) = (r.num : ZMod p) := by
    simpa only [aligns, Int.cast_natCast] using ha
  constructor
  · intro ht
    rw [ht]
    exact ha'
  · intro ht
    exact mul_left_cancel₀ hD (ht.trans ha'.symm)

theorem squarefree_int_modEq_iff (d : ℕ) (hd : Squarefree d) (x y : ℤ) :
    Int.ModEq (d : ℤ) x y ↔ ∀ p ∈ d.primeFactors, Int.ModEq (p : ℤ) x y := by
  simp only [Int.modEq_iff_dvd, Int.natCast_dvd]
  have h := modEq_prime_product_iff d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (y-x).natAbs 0
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  simpa only [Nat.modEq_zero_iff_dvd] using h

theorem required_hits_iff_parameter (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    (∀ p ∈ d.primeFactors, t % p = a p % p) ↔
      ∃ m : ℤ, (r.den : ℤ)*(t : ℤ) = r.num+(d : ℤ)*m := by
  have hp : (∀ p ∈ d.primeFactors, t % p = a p % p) ↔
      ∀ p ∈ d.primeFactors, Int.ModEq (p : ℤ) ((r.den : ℤ)*(t : ℤ)) r.num := by
    exact forall_congr' (fun p => forall_congr' (fun h =>
      aligned_prime_hit_iff a r p t (Nat.prime_of_mem_primeFactors h) (ha p h)))
  rw [hp, ← squarefree_int_modEq_iff d hd, Int.modEq_comm, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩

end ErdosAlignedProgression

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

section

namespace NumberTheoryLean.EulerProductRatio

open scoped BigOperators

theorem restricted_block_union (z K : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ z)
    (hlower : ∀ p ∈ P, 2 ^ (2 ^ K) ≤ p) :
    (Finset.Icc K (PrimeDensityBlocks.lastBlock z)).biUnion (PrimeDensityBlocks.primeBlock P) = P := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpj).1
  · intro hp
    have hfull := PrimeDensityBlocks.primeBlock_union z P hprime hsize
    have hpFull : p ∈ (PrimeDensityBlocks.blockIndices z).biUnion (PrimeDensityBlocks.primeBlock P) := by
      simpa only [hfull] using hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpFull
    have hjJ : j ≤ PrimeDensityBlocks.lastBlock z := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hKj : K ≤ j := by
      by_contra hnot
      have hjK : j + 1 ≤ K := by omega
      have he : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
      have htop : 2 ^ (2 ^ (j + 1)) ≤ 2 ^ (2 ^ K) := Nat.pow_le_pow_right (by norm_num) he
      have hbelow := (PrimeDensityBlocks.mem_geometricPrimes.mp (Finset.mem_inter.mp hpj).2).2.1
      have habove := hlower p hp
      omega
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hKj, hjJ⟩, hpj⟩

theorem tail_euler_lower (z h : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ z)
    (hlower : ∀ p ∈ P, 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ p) :
    Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  let J := PrimeDensityBlocks.lastBlock z
  let B := Finset.Icc (J - h) J
  have hdim : ∀ p ∈ P, (p : ℝ)⁻¹ ≤ 2 / p := by
    intro p _
    simpa only [one_div] using div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_nonneg p)
  have hcap := BonferroniDensity.prime_density_le_two_thirds P (fun p => (p : ℝ)⁻¹)
    hprime hdim (fun _ => by norm_num)
  have heach : ∀ j ∈ B, Real.exp (-4596) ≤
      ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - (p : ℝ)⁻¹) := by
    intro j _
    have hsum := PrimeDensityBlocks.primeBlock_density_sum_le P j (fun p => (p : ℝ)⁻¹) hdim
    have he := BonferroniDensity.exp_neg_three_mul_le_eulerProduct (PrimeDensityBlocks.primeBlock P j)
      (fun p => (p : ℝ)⁻¹) (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
      (fun p hp => hcap p (Finset.mem_inter.mp hp).1) hsum
    norm_num at he
    exact he
  have hcard : B.card ≤ h + 1 := by
    dsimp [B]
    rw [Nat.card_Icc]
    omega
  have hdis : (B : Set ℕ).PairwiseDisjoint (PrimeDensityBlocks.primeBlock P) := by
    intro i _ j _ hij
    exact (PrimeDensityBlocks.geometricPrimes_disjoint hij).mono Finset.inter_subset_right Finset.inter_subset_right
  calc
    Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤ Real.exp (-4596 * (B.card : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hc : (B.card : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      linarith
    _ = ∏ _j ∈ B, Real.exp (-4596) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ∏ j ∈ B, ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - (p : ℝ)⁻¹) :=
      Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) heach
    _ = _ := by rw [← Finset.prod_biUnion hdis, restricted_block_union z (J - h) P hprime hsize hlower]

theorem smallEuler_nonneg (z : ℕ) : 0 ≤ SmallSieveFinite.smallEuler z := by
  apply Finset.prod_nonneg
  intro p hp
  apply sub_nonneg.mpr
  have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hprime.one_lt.le)

theorem smallEuler_ratio_nat (z t h : ℕ) (htz : t ≤ z)
    (hlower : 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ t) :
    SmallSieveFinite.smallEuler t ≤ Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler z := by
  classical
  let Pz := LargePrimeDeletion.cutoffPrimes z
  let Pt := LargePrimeDeletion.cutoffPrimes t
  let Q := Pz \ Pt
  have hsub : Pt ⊆ Pz := by
    intro p hp
    obtain ⟨hpp, hpt⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨hpp, hpt.trans htz⟩
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp hp).1).1
  have hsize : ∀ p ∈ Q, p ≤ z := fun p hp =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp hp).1).2
  have hQlow : ∀ p ∈ Q, 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ p := by
    intro p hp
    have hn := (Finset.mem_sdiff.mp hp).2
    have hpp := hprime p hp
    have htp : t < p := by
      by_contra hnot
      exact hn (LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨hpp, Nat.le_of_not_lt hnot⟩)
    exact hlower.trans htp.le
  have he := tail_euler_lower z h Q hprime hsize hQlow
  have hprod : SmallSieveFinite.smallEuler z =
      SmallSieveFinite.smallEuler t * ∏ p ∈ Q, (1 - (p : ℝ)⁻¹) := by
    unfold SmallSieveFinite.smallEuler
    rw [← Finset.prod_sdiff hsub]
    ring
  have hmul : SmallSieveFinite.smallEuler t * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤
      SmallSieveFinite.smallEuler z := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left he (smallEuler_nonneg t)
  have hfinal := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (4596 * ((h + 1 : ℕ) : ℝ))).le
  have hcancel : Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) *
      (SmallSieveFinite.smallEuler t * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ))) = SmallSieveFinite.smallEuler t := by
    calc
      _ = SmallSieveFinite.smallEuler t *
          (Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  rw [hcancel] at hfinal
  exact hfinal

theorem rootExponent_pos (h : ℕ) : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ)⁻¹ := by positivity

theorem rootExponent_le_one (h : ℕ) : ((2 ^ h : ℕ) : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_pow h 2 (by norm_num))

theorem rootCutoff_le (u : ℝ) (h : ℕ) (hu : 1 ≤ u) : rootCutoff u h ≤ u :=
  Real.rpow_le_self_of_one_le hu (rootExponent_le_one h)

theorem rootCutoff_ge_two (u : ℝ) (h : ℕ) (hu : (2 : ℝ) ^ (2 ^ h : ℕ) ≤ u) :
    2 ≤ rootCutoff u h := by
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ h : ℕ)) hu (rootExponent_pos h).le
  rw [Real.pow_rpow_inv_natCast (by norm_num) (pow_ne_zero h (by norm_num : (2 : ℕ) ≠ 0))] at hroot
  exact hroot

theorem geometric_endpoint_le_rootCutoff (u : ℝ) (h : ℕ) (hu : 2 ≤ u) (hw : 2 ≤ rootCutoff u h) :
    ((2 ^ (2 ^ (PrimeDensityBlocks.lastBlock ⌊u⌋₊ - h)) : ℕ) : ℝ) ≤ rootCutoff u h := by
  let z := ⌊u⌋₊
  let J := PrimeDensityBlocks.lastBlock z
  have hz : 2 ≤ z := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  by_cases hhJ : h ≤ J
  · let n := 2 ^ (2 ^ (J - h))
    have hpow : n ^ (2 ^ h) = 2 ^ (2 ^ J) := by
      dsimp [n]
      have he : 2 ^ (J - h) * 2 ^ h = 2 ^ J := by rw [← pow_add, Nat.sub_add_cancel hhJ]
      rw [← pow_mul, he]
    have hbaseN : n ^ (2 ^ h) ≤ z := hpow ▸ PrimeDensityBlocks.lastBlock_lower_le z hz
    have hbaseR : (n : ℝ) ^ (2 ^ h : ℕ) ≤ u := by
      have hcast : (n : ℝ) ^ (2 ^ h : ℕ) ≤ (z : ℝ) := by exact_mod_cast hbaseN
      exact hcast.trans (Nat.floor_le (by linarith))
    have hroot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg n) _) hbaseR (rootExponent_pos h).le
    rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg n) (pow_ne_zero h (by norm_num : (2 : ℕ) ≠ 0))] at hroot
    exact hroot
  · have hJh : J ≤ h := by omega
    have hzero : J - h = 0 := Nat.sub_eq_zero_of_le hJh
    change ((2 ^ (2 ^ (J - h)) : ℕ) : ℝ) ≤ _
    simpa only [hzero, pow_zero, pow_one, Nat.cast_ofNat] using hw

theorem smallEuler_ratio_rootCutoff (u : ℝ) (h : ℕ) (hu : 2 ≤ u) (hw : 2 ≤ rootCutoff u h) :
    SmallSieveFinite.smallEuler ⌊rootCutoff u h⌋₊ ≤
      Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  apply smallEuler_ratio_nat
  · exact Nat.floor_mono (rootCutoff_le u h (by linarith))
  · apply (Nat.le_floor_iff (by linarith : 0 ≤ rootCutoff u h)).mpr
    exact geometric_endpoint_le_rootCutoff u h hu hw

end NumberTheoryLean.EulerProductRatio

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



namespace NumberTheoryLean.SmallSieveUpper

theorem cutoffSurvivors_antitone (N z t : ℕ) (htz : t ≤ z) (residue : ℕ → ℕ) :
    LargePrimeDeletion.cutoffSurvivors N z residue ⊆ LargePrimeDeletion.cutoffSurvivors N t residue := by
  intro i hi
  obtain ⟨hiN, hav⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp hi
  exact LargePrimeDeletion.mem_cutoffSurvivors.mpr ⟨hiN, fun p hp hpt => hav p hp (hpt.trans htz)⟩

theorem count_le_four_of_relative (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u) :
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      4 * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  have h := SmallSieveRelative.small_relative N u J residue hu hJ hNJ hv
  have hExp : Real.exp (-(Real.log J / Real.log u) / 192) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have hEuler : 0 < SmallSieveFinite.smallEuler ⌊u⌋₊ :=
    (inv_pos.mpr (show 0 < u by linarith)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv u hu)
  have hDen : 0 < J * SmallSieveFinite.smallEuler ⌊u⌋₊ := mul_pos hJ hEuler
  have hRatio := (abs_le.mp h).2
  have hBound : ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      4 * (J * SmallSieveFinite.smallEuler ⌊u⌋₊) := (div_le_iff₀ hDen).mp (by linarith)
  simpa only [mul_assoc] using hBound

theorem threshold_ge_two (h : ℕ) : (2 : ℝ) ≤ (2 : ℝ) ^ (2 ^ h : ℕ) := by
  have hn : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  simpa only [pow_one] using hp

theorem small_upper_explicit (N : ℕ) (u J η : ℝ) (residue : ℕ → ℕ) (h : ℕ)
    (hscale : 960048 ≤ η * ((2 ^ h : ℕ) : ℝ))
    (hu : (2 : ℝ) ^ (2 ^ h : ℕ) ≤ u) (hJlower : u ^ η ≤ J) (hNJ : |(N : ℝ) - J| ≤ 1) :
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      (4 * Real.exp (4596 * ((h + 1 : ℕ) : ℝ))) * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  let w := EulerProductRatio.rootCutoff u h
  have hu2 : 2 ≤ u := (threshold_ge_two h).trans hu
  have hu0 : 0 < u := by linarith
  have hw2 : 2 ≤ w := EulerProductRatio.rootCutoff_ge_two u h hu
  have hwle : w ≤ u := EulerProductRatio.rootCutoff_le u h (by linarith)
  have hJ : 0 < J := (Real.rpow_pos_of_pos hu0 η).trans_le hJlower
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hn : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ) := by positivity
  have hη : 960048 * (((2 ^ h : ℕ) : ℝ)⁻¹) ≤ η := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hn).mpr hscale
  have hlogJ : η * Real.log u ≤ Real.log J := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hu0 η) hJlower
    rwa [Real.log_rpow hu0] at hlog
  have hlogw : Real.log w = (((2 ^ h : ℕ) : ℝ)⁻¹) * Real.log u := Real.log_rpow hu0 _
  have hvw : 960048 ≤ Real.log J / Real.log w := by
    apply (le_div_iff₀ hlw).mpr
    rw [hlogw]
    have hmul := mul_le_mul_of_nonneg_right hη hlu.le
    nlinarith
  have hCount := count_le_four_of_relative N w J residue hw2 hJ hNJ hvw
  have hEuler := EulerProductRatio.smallEuler_ratio_rootCutoff u h hu2 hw2
  have hSubset := cutoffSurvivors_antitone N ⌊u⌋₊ ⌊w⌋₊ (Nat.floor_mono hwle) residue
  calc
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
        ((LargePrimeDeletion.cutoffSurvivors N ⌊w⌋₊ residue).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset
    _ ≤ 4 * J * SmallSieveFinite.smallEuler ⌊w⌋₊ := hCount
    _ ≤ 4 * J * (Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler ⌊u⌋₊) :=
      mul_le_mul_of_nonneg_left hEuler (by positivity)
    _ = _ := by ring

theorem small_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 2 ≤ u₀ ∧
      ∀ (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ), u₀ ≤ u → u ^ η ≤ J →
        |(N : ℝ) - J| ≤ 1 →
        ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
          C * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  obtain ⟨h, hh⟩ := pow_unbounded_of_one_lt (960048 / η) (by norm_num : (1 : ℝ) < 2)
  have hscale : 960048 ≤ η * ((2 ^ h : ℕ) : ℝ) := by
    have hmul := (div_lt_iff₀ hη).mp hh
    push_cast
    nlinarith
  refine ⟨4 * Real.exp (4596 * ((h + 1 : ℕ) : ℝ)), by positivity,
    (2 : ℝ) ^ (2 ^ h : ℕ), threshold_ge_two h, ?_⟩
  intro N u J residue hu hJ hNJ
  exact small_upper_explicit N u J η residue h hscale hu hJ hNJ

theorem progression_small_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 2 ≤ u₀ ∧
      ∀ (N : ℕ) (u J : ℝ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ),
        u₀ ≤ u → u ^ η ≤ J → |(N : ℝ) - J| ≤ 1 →
        (∀ p : ℕ, p.Prime → (p : ℝ) ≤ u → q.Coprime p) →
        ((ProgressionSmallSieve.progressionSurvivors N ⌊u⌋₊ a q residue).card : ℝ) ≤
          C * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  obtain ⟨C, hC, u₀, hu₀, hBound⟩ := small_upper η hη
  refine ⟨C, hC, u₀, hu₀, ?_⟩
  intro N u J a q residue hu hJ hNJ hcop
  have hcopNat : ∀ p : ℕ, p.Prime → p ≤ ⌊u⌋₊ → q.Coprime p := by
    intro p hp hpu
    exact hcop p hp ((Nat.le_floor_iff (by linarith)).mp hpu)
  obtain ⟨transformed, hEq⟩ := ProgressionSmallSieve.exists_progressionSurvivors_eq N ⌊u⌋₊ a q residue hcopNat
  rw [hEq]
  exact hBound N u J transformed hu hJ hNJ

end NumberTheoryLean.SmallSieveUpper



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HypotheticalIndividualUpper
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosInverseCounts ErdosInverseHits ErdosModulusRelative

theorem original_individual_upper :
    ∃ C : ℝ,0 < C ∧ ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P0 ≤ P →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ t ∈ d.primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(d : ℝ) →
        (modulusCount Y (LargePrimeDeletion.cutoffPrimes (P-1)) a d : ℝ) ≤
          C*((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler (P-1) := by
  obtain ⟨C,hC,u0,hu0,hUpper⟩ := SmallSieveUpper.progression_small_upper 2 (by norm_num)
  refine ⟨C,hC,⌈u0⌉₊+3,by omega,?_⟩
  intro P hP Y d a _hY hd hlarge hJ
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hP0 : 0 < P := by omega
  have hU : u0 ≤ ((P-1 : ℕ) : ℝ) := by
    exact (Nat.le_ceil u0).trans (by exact_mod_cast (show ⌈u0⌉₊ ≤ P-1 by omega))
  have hUp : ((P-1 : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast Nat.sub_lt hP0 (by decide : 0 < 1)
  have hU0 : 0 ≤ ((P-1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow : ((P-1 : ℕ) : ℝ)^(2 : ℝ) ≤ (Y : ℝ)/(d : ℝ) := by
    rw [Real.rpow_two]
    exact (pow_le_pow_left₀ hU0 hUp.le 2).trans hJ
  have hcop (t : ℕ) (ht : t.Prime) (htu : (t : ℝ) ≤ ((P-1 : ℕ) : ℝ)) : d.Coprime t := by
    apply large_modulus_coprime_small ((P-1 : ℕ) : ℝ) d hd _ t ht htu
    intro q hq
    exact hUp.trans_le (by exact_mod_cast hlarge q hq)
  have hb := primeHitRepresentative_spec d hd a
  have hN := hitLength_error Y d (primeHitRepresentative d hd a) hd0 hb.1 hb.2.1
  have hh := hUpper (hitLength Y d (primeHitRepresentative d hd a)) ((P-1 : ℕ) : ℝ)
    ((Y : ℝ)/(d : ℝ)) (primeHitRepresentative d hd a : ℤ) d a hU hpow hN hcop
  simp only [Nat.floor_natCast] at hh
  rw [modulus_count_eq_offsets Y _ a d hd,offsets_eq_progression,Int.cast_natCast]
  exact hh

end ErdosStoppedArithmetic

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

lemma mem_primeMultiplesIn (d : ℕ) (P x y : ℝ) (m : ℤ) :
    m ∈ primeMultiplesIn d P x y ↔ x < (m:ℝ) ∧ (m:ℝ) < y ∧
      ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)) := by
  classical
  constructor
  · intro hm
    exact (mem_filter.mp hm).2
  · intro hm
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨Int.ceil_le.mpr hm.1.le,Int.le_floor.mpr hm.2.1.le⟩,hm⟩

end Erdos970Dependency.SiegelWalfisz



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

theorem admissible_pair_card_rows (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    (admissiblePairs T M good).card = ∑ p ∈ T,(M.filter (good p)).card := by
  simp only [admissiblePairs,Finset.card_filter,Finset.product_eq_sprod,Finset.sum_product]

end ErdosStoppedArithmetic



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RationalParameterInterval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
attribute [local instance] Classical.decEq

theorem mem_parameterInterval (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ) :
    m ∈ parameterInterval Y r d ↔
      (r.den : ℤ) ≤ r.num+(d : ℤ)*m ∧ r.num+(d : ℤ)*m ≤ (r.den : ℤ)*(Y : ℤ) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  rw [parameterInterval, Finset.mem_Icc]
  have hl : parameterLower r d ≤ m ↔ (r.den : ℤ) ≤ r.num+(d : ℤ)*m := by
    unfold parameterLower
    constructor
    · intro h
      have hn : -m ≤ (r.num-(r.den : ℤ))/(d : ℤ) := by linarith
      have hh := (Int.le_ediv_iff_mul_le hdZ).mp hn
      nlinarith
    · intro h
      have hn : -m ≤ (r.num-(r.den : ℤ))/(d : ℤ) := by
        apply (Int.le_ediv_iff_mul_le hdZ).mpr
        nlinarith
      linarith
  have hu : m ≤ parameterUpper Y r d ↔ r.num+(d : ℤ)*m ≤ (r.den : ℤ)*(Y : ℤ) := by
    unfold parameterUpper
    rw [Int.le_ediv_iff_mul_le hdZ]
    constructor <;> intro h <;> nlinarith
  exact and_congr hl hu

theorem parameterValue_spec (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hm : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    1 ≤ parameterValue r d m ∧ parameterValue r d m ≤ Y ∧
      (r.den : ℤ)*(parameterValue r d m : ℤ) = r.num+(d : ℤ)*m := by
  have hb := (mem_parameterInterval Y r d hd m).mp hm
  have hD : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hquot : (1 : ℤ) ≤ (r.num+(d : ℤ)*m)/(r.den : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hD).mpr
    simpa only [one_mul] using hb.1
  have hcast : (parameterValue r d m : ℤ) = (r.num+(d : ℤ)*m)/(r.den : ℤ) :=
    Int.toNat_of_nonneg (by linarith)
  have he : (r.den : ℤ)*(parameterValue r d m : ℤ) = r.num+(d : ℤ)*m := by
    rw [hcast]
    exact Int.mul_ediv_cancel_of_dvd hdiv
  have hlo : (1 : ℤ) ≤ parameterValue r d m := by rw [hcast]; exact hquot
  have hhi : (parameterValue r d m : ℤ) ≤ Y := by
    have hm : (r.den : ℤ)*(parameterValue r d m : ℤ) ≤ (r.den : ℤ)*(Y : ℤ) := by
      rw [he]
      exact hb.2
    nlinarith
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi, he⟩

end ErdosAlignedProgression

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RationalCandidateSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment

theorem parameterOf_spec (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : ∀ p ∈ d.primeFactors, t % p = a p % p) :
    (r.den : ℤ)*(t : ℤ) = r.num+(d : ℤ)*parameterOf r d t := by
  obtain ⟨m, hm⟩ := (required_hits_iff_parameter a r d t hd ha).mp ht
  have hdiv : (d : ℤ) ∣ (r.den : ℤ)*(t : ℤ)-r.num := ⟨m, by linarith⟩
  have he := Int.mul_ediv_cancel_of_dvd hdiv
  dsimp only [parameterOf]
  linarith

theorem parameterValue_parameterOf (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : ∀ p ∈ d.primeFactors, t % p = a p % p) :
    parameterValue r d (parameterOf r d t) = t := by
  have he := parameterOf_spec a r d t hd ha ht
  have hD : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [parameterValue, ← he, Int.mul_ediv_cancel_left _ hD, Int.toNat_natCast]

theorem parameterOf_parameterValue (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hm : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    parameterOf r d (parameterValue r d m) = m := by
  have hs := parameterValue_spec Y r d hd m hm hdiv
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [parameterOf, hs.2.2, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hdZ]

end ErdosAlignedProgression

end

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem parameterOf_mem (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : t ∈ modulusCandidates Y small a d) :
    parameterOf r d t ∈ parameterCandidates Y small a r d := by
  obtain ⟨ht1, htY, hhit, hsmall⟩ := (mem_modulusCandidates Y small a d t).mp ht
  have he := parameterOf_spec a r d t hd ha hhit
  have hD : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have ht1Z : (1 : ℤ) ≤ t := by exact_mod_cast ht1
  have htYZ : (t : ℤ) ≤ Y := by exact_mod_cast htY
  apply Finset.mem_filter.mpr
  refine ⟨(mem_parameterInterval Y r d (Nat.pos_of_ne_zero hd.ne_zero) _).mpr ?_, ?_, ?_⟩
  · rw [← he]
    constructor <;> nlinarith
  · exact ⟨(t : ℤ), he.symm⟩
  · rw [parameterValue_parameterOf a r d t hd ha hhit]
    exact hsmall

theorem parameterValue_mem (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (m : ℤ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (hm : m ∈ parameterCandidates Y small a r d) :
    parameterValue r d m ∈ modulusCandidates Y small a d := by
  obtain ⟨hI, hdiv, hsmall⟩ := Finset.mem_filter.mp hm
  have hs := parameterValue_spec Y r d (Nat.pos_of_ne_zero hd.ne_zero) m hI hdiv
  apply (mem_modulusCandidates Y small a d _).mpr
  exact ⟨hs.1, hs.2.1, (required_hits_iff_parameter a r d _ hd ha).mpr ⟨m, hs.2.2⟩, hsmall⟩

theorem parameterCandidates_eq_image (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    parameterCandidates Y small a r d =
      (modulusCandidates Y small a d).image (parameterOf r d) := by
  ext m
  constructor
  · intro hm
    have ht := parameterValue_mem Y small a r d m hd ha hm
    obtain ⟨hI, hdiv, _hsmall⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_image.mpr ⟨parameterValue r d m, ht,
      parameterOf_parameterValue Y r d (Nat.pos_of_ne_zero hd.ne_zero) m hI hdiv⟩
  · intro hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
    exact parameterOf_mem Y small a r d t hd ha ht

theorem parameterOf_injOn (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    Set.InjOn (parameterOf r d) (modulusCandidates Y small a d : Set ℕ) := by
  intro t ht u hu he
  have ht' := ((mem_modulusCandidates Y small a d t).mp ht).2.2.1
  have hu' := ((mem_modulusCandidates Y small a d u).mp hu).2.2.1
  calc
    t = parameterValue r d (parameterOf r d t) := (parameterValue_parameterOf a r d t hd ha ht').symm
    _ = parameterValue r d (parameterOf r d u) := congrArg (parameterValue r d) he
    _ = u := parameterValue_parameterOf a r d u hd ha hu'

theorem modulusCount_eq_parameter_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    modulusCount Y small a d = ((parameterCandidates Y small a r d).card : ℤ) := by
  rw [modulusCount, parameterCandidates_eq_image Y small a r d hd ha,
    Finset.card_image_of_injOn (parameterOf_injOn Y small a r d hd ha)]

end ErdosAlignedProgression

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_HypotheticalResidues
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts
attribute [local instance] Classical.decEq

theorem hypothetical_other (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p]
    (s : ℕ) (hsp : s ≠ p) : hypotheticalClass a r p s = a s :=
  Function.update_of_ne hsp _ _

theorem hypothetical_aligns (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hD : r.den.Coprime p) :
    aligns (fun s => (hypotheticalClass a r p s : ℤ)) r p := by
  let : Fact p.Prime := ⟨hp⟩
  have hd0 : (r.den : ZMod p) ≠ 0 := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp hD.symm) ((ZMod.natCast_eq_zero_iff _ _).mp h)
  simp only [aligns, hypotheticalClass, Function.update_self, hypotheticalResidue,
    Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_left_comm, mul_inv_cancel₀ hd0, mul_one]

theorem hypothetical_mod_agrees (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) (s : ℕ) :
    hypotheticalClass a r p s % s = a s % s := by
  by_cases hsp : s = p
  · subst s
    have hD := aligned_den_coprime_prime a r p hp ha
    have hh := hypothetical_aligns a r p hp hD
    exact (aligned_prime_hit_iff a r p (hypotheticalClass a r p p) hp ha).mpr
      ((aligns_iff_modEq (fun s => (hypotheticalClass a r p s : ℤ)) r p).mp hh)
  · rw [hypothetical_other a r p s hsp]

theorem hypothetical_candidates_agree (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    modulusCandidates Y small (hypotheticalClass a r p) d = modulusCandidates Y small a d := by
  ext t
  simp only [mem_modulusCandidates, hypothetical_mod_agrees a r p hp ha]

theorem hypothetical_count_agrees (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    modulusCount Y small (hypotheticalClass a r p) d = modulusCount Y small a d := by
  rw [modulusCount, modulusCount, hypothetical_candidates_agree Y small a r d p hp ha]

end ErdosHypotheticalTag

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


namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts
attribute [local instance] Classical.decEq

theorem hypothetical_small_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p ∉ small) :
    parameterCandidates Y small (hypotheticalClass a r p) r d = parameterCandidates Y small a r d := by
  ext m
  simp only [parameterCandidates, Finset.mem_filter]
  apply and_congr_right
  intro _hI
  apply and_congr_right
  intro _hdiv
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  have hsp : s ≠ p := by intro h; subst s; exact hp hs
  rw [hypothetical_other a r p s hsp]

theorem hypothetical_count_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hd : Squarefree d) (hp : p.Prime)
    (hD : r.den.Coprime p) (hsmall : p ∉ small)
    (hother : ∀ s ∈ d.primeFactors, s ≠ p → aligns (fun u => (a u : ℤ)) r s) :
    modulusCount Y small (hypotheticalClass a r p) d = ((parameterCandidates Y small a r d).card : ℤ) := by
  have hall : ∀ s ∈ d.primeFactors, aligns (fun u => (hypotheticalClass a r p u : ℤ)) r s := by
    intro s hs
    by_cases hsp : s = p
    · subst s
      exact hypothetical_aligns a r p hp hD
    · simpa only [aligns, hypothetical_other a r p s hsp] using hother s hs hsp
  rw [modulusCount_eq_parameter_card Y small (hypotheticalClass a r p) r d hd hall,
    hypothetical_small_parameters Y small a r d p hsmall]

end ErdosHypotheticalTag


namespace ErdosStoppedArithmetic
open ErdosAlignedProgression ErdosHypotheticalTag ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem hypothetical_row_parameters (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T)
    (hsf : Squarefree (p.val*q)) (hD : r.den.Coprime p.val) (hsmall : p.val ∉ small)
    (hother : ∀ t ∈ (p.val*q).primeFactors,t ≠ p.val → aligns (fun u => (a u : ℤ)) r t) :
    hypotheticalRowCount Y small T a r q hT p = ((parameterCandidates Y small a r (p.val*q)).card : ℝ) := by
  let : NeZero p.val := ⟨(hT p.val p.property).ne_zero⟩
  unfold hypotheticalRowCount
  rw [hypothetical_count_parameters Y small a r (p.val*q) p.val hsf (hT p.val p.property) hD hsmall hother,
    Int.cast_natCast]

theorem parameter_value_integer (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hI : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    (parameterValue r d m : ℤ)=(r.num+(d : ℤ)*m)/(r.den : ℤ) := by
  have hs := parameterValue_spec Y r d hd m hI hdiv
  have hD : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [← hs.2.2,Int.mul_ediv_cancel_left _ hD]

theorem actual_test_mem_parameters (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ) (hI : m ∈ parameterInterval Y r d)
    (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m)
    (hAvoid : ∀ t ∈ small,¬Int.ModEq (t : ℤ) ((r.num+(d : ℤ)*m)/(r.den : ℤ)) (a t : ℤ)) :
    m ∈ parameterCandidates Y small a r d := by
  apply Finset.mem_filter.mpr
  refine ⟨hI,hdiv,?_⟩
  intro t ht he
  have hNat : Nat.ModEq t (parameterValue r d m) (a t) := he
  have hInt : Int.ModEq (t : ℤ) (parameterValue r d m : ℤ) (a t : ℤ) :=
    (Int.natCast_modEq_iff).mpr hNat
  rw [parameter_value_integer Y r d hd m hI hdiv] at hInt
  exact hAvoid t ht hInt

theorem pair_count_le_hypothetical_sum (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (M : Finset ℤ) (good : ℕ → ℤ → Prop)
    (hGeometry : ∀ p ∈ T,Squarefree (p*q) ∧ r.den.Coprime p ∧ p ∉ small ∧
      ∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t)
    (hCommon : ∀ p ∈ T,∀ m ∈ M,good p m → m ∈ parameterInterval Y r (p*q))
    (hGood : ∀ p ∈ T,∀ m ∈ M,good p m →
      (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m ∧
      ∀ t ∈ small,¬Int.ModEq (t : ℤ) ((r.num+((p*q : ℕ) : ℤ)*m)/(r.den : ℤ)) (a t : ℤ)) :
    ((admissiblePairs T M good).card : ℝ) ≤ ∑ p : T,hypotheticalRowCount Y small T a r q hT p := by
  have hRows : (admissiblePairs T M good).card ≤
      ∑ p ∈ T,(parameterCandidates Y small a r (p*q)).card := by
    rw [admissible_pair_card_rows]
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.card_le_card
    intro m hm
    have hmM := (Finset.mem_filter.mp hm).1
    have hcond := hGood p hp m hmM (Finset.mem_filter.mp hm).2
    exact actual_test_mem_parameters Y small a r (p*q)
      (Nat.pos_of_ne_zero (hGeometry p hp).1.ne_zero) m (hCommon p hp m hmM (Finset.mem_filter.mp hm).2) hcond.1 hcond.2
  calc
    _ ≤ ∑ p ∈ T,((parameterCandidates Y small a r (p*q)).card : ℝ) := by exact_mod_cast hRows
    _ = ∑ p : T,((parameterCandidates Y small a r (p.val*q)).card : ℝ) := (Finset.sum_coe_sort T _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      have hg := hGeometry p.val p.property
      exact (hypothetical_row_parameters Y small T a r q hT p hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).symm

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagSubbinWidths
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
namespace ErdosTagSubbins

theorem count_bounds {w Cs : ℝ} (hw : 1 < w) (hCs : 0 ≤ Cs) :
    1 ≤ count w Cs ∧ w ^ (2 * Cs + 10) ≤ (count w Cs : ℝ) ∧
    (count w Cs : ℝ) ≤ 2 * w ^ (2 * Cs + 10) := by
  have hp : 1 ≤ w ^ (2 * Cs + 10) := Real.one_le_rpow hw.le (by linarith)
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have h := Nat.ceil_lt_add_one (le_trans (by norm_num) hp)
  dsimp [count]
  linarith

theorem right_upper {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hi : i < N) : right R theta N i ≤ (1 + theta) * R := by
  have hN : 0 < N := Nat.zero_lt_of_lt hi
  have hs := step_pos hR ht hN
  have hi' : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hi
  have h := mul_le_mul_of_nonneg_right hi' hs.le
  rw [total_step hN] at h
  dsimp [right]; nlinarith only [h]

theorem left_lt_right {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : left R theta N i < right R theta N i := by
  rw [right_eq_left_add]; linarith [step_pos hR ht hN]

end ErdosTagSubbins

end

section

namespace ErdosTagSubbins

theorem width_le_theta_div {R theta : ℝ} {N i : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) : width R theta N i ≤ theta / N := by
  have hl := left_lower (i := i) (step_pos hR ht hN).le
  have hs := step_pos hR ht hN
  calc
    width R theta N i ≤ step R theta N / R := div_le_div_of_nonneg_left hs.le hR hl
    _ = theta / N := by unfold step; field_simp

theorem width_upper {R theta w Cs : ℝ} {i : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hw : 1 < w) (hCs : 0 ≤ Cs) :
    width R theta (count w Cs) i ≤ w ^ (-2 * Cs - 10) := by
  have hb := count_bounds hw hCs
  have hN : 0 < count w Cs := hb.1
  have hq : 0 < w ^ (2 * Cs + 10) := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ theta / (count w Cs : ℝ) := width_le_theta_div hR ht hN
    _ ≤ 1 / (count w Cs : ℝ) := div_le_div_of_nonneg_right ht1 (by positivity)
    _ ≤ 1 / w ^ (2 * Cs + 10) := div_le_div_of_nonneg_left (by norm_num) hq hb.2.1
    _ = w ^ (-2 * Cs - 10) := by
      rw [show -2 * Cs - 10 = -(2 * Cs + 10) by ring, Real.rpow_neg (by linarith : 0 ≤ w)]
      exact one_div _

theorem width_lower {R theta w Cs xi : ℝ} {i : ℕ} (hR : 0 < R)
    (hxi : 0 < xi) (htxi : xi / 4 ≤ theta) (ht1 : theta ≤ 1)
    (hw : 1 < w) (hCs : 0 ≤ Cs) (hi : i < count w Cs) :
    xi / (16 * w ^ (2 * Cs + 10)) ≤ width R theta (count w Cs) i := by
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le htxi
  have hb := count_bounds hw hCs
  have hN : 0 < count w Cs := hb.1
  have hNr : (0 : ℝ) < count w Cs := by exact_mod_cast hN
  have hq : 0 < w ^ (2 * Cs + 10) := Real.rpow_pos_of_pos (by linarith) _
  have hl := left_pos (i := i) hR ht hN
  have hlu : left R theta (count w Cs) i ≤ 2 * R := by
    have h := (left_lt_right (i := i) hR ht hN).le.trans (right_upper hR ht hi)
    nlinarith only [h, mul_le_mul_of_nonneg_right ht1 hR.le]
  calc
    xi / (16 * w ^ (2 * Cs + 10)) ≤ theta / (4 * w ^ (2 * Cs + 10)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right htxi (show 0 ≤ 16 * w ^ (2 * Cs + 10) by positivity)
      nlinarith only [h]
    _ ≤ theta / (2 * (count w Cs : ℝ)) := by
      apply div_le_div_of_nonneg_left ht.le (by positivity)
      linarith only [hb.2.2]
    _ = step R theta (count w Cs) / (2 * R) := by unfold step; field_simp
    _ ≤ width R theta (count w Cs) i := div_le_div_of_nonneg_left
      (step_pos hR ht hN).le hl hlu

end ErdosTagSubbins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_CanonicalTagPrimePartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins
open ErdosInversePrimeBin

theorem subbin_subset {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hi : i < N) : subbin R theta N i ⊆ primeBin R theta := by
  intro p hp
  have hN : 0 < N := Nat.zero_lt_of_lt hi
  obtain ⟨hprime, hlo, hhi⟩ := (mem_subbin hR ht hN).mp hp
  exact (mem_primeBin hR.le ht.le p).mpr ⟨hprime,
    (left_lower (step_pos hR ht hN).le).trans_lt hlo, hhi.trans (right_upper hR ht hi)⟩

theorem subbins_pairwise_disjoint {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) :
    Pairwise (fun i j : Fin N => Disjoint (subbin R theta N i) (subbin R theta N j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hp := subbin_subset hR ht i.isLt hpi
  obtain ⟨k, _, hk⟩ := unique_prime_subbin hR ht hN hp
  exact hij ((hk i hpi).trans (hk j hpj).symm)

theorem finite_partition {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) :
    (Finset.univ : Finset (Fin N)).biUnion (fun i => subbin R theta N i) = primeBin R theta := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact subbin_subset hR ht i.isLt hi
  · intro hp
    exact (unique_prime_subbin hR ht hN hp).exists

theorem sum_partition {R theta : ℝ} {N : ℕ} {B : Type*} [AddCommMonoid B]
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) (reward : ℕ → B) :
    (∑ p ∈ primeBin R theta, reward p) =
      ∑ i : Fin N, ∑ p ∈ subbin R theta N i, reward p := by
  classical
  rw [← finite_partition hR ht hN]
  exact Finset.sum_biUnion (fun i _ j _ hij => subbins_pairwise_disjoint hR ht hN hij)

end ErdosTagSubbins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonSliceGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosCommonParameterInterval

theorem div_between_endpoints (a : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    min (a/R) (a/T) ≤ a/p ∧ a/p ≤ max (a/R) (a/T) := by
  have hp : 0 < p := hR.trans_le hRp
  have hT : 0 < T := hp.trans_le hpT
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_right _ _).trans (div_le_div_of_nonneg_left ha hp hpT),
      (div_le_div_of_nonneg_left ha hR hRp).trans (le_max_left _ _)⟩
  · have han : 0 ≤ -a := by linarith
    have h1 := div_le_div_of_nonneg_left han hp hpT
    have h2 := div_le_div_of_nonneg_left han hR hRp
    simp only [neg_div] at h1 h2
    exact ⟨(min_le_left _ _).trans (by linarith),
      (show a/p ≤ a/T by linarith).trans (le_max_right _ _)⟩

theorem common_interval_subset (a b : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    Set.Ioc (commonLower a R T) (commonUpper b R T) ⊆ Set.Ioc (a/p) (b/p) := by
  intro m hm
  exact ⟨(div_between_endpoints a hR hRp hpT).2.trans_lt hm.1,
    hm.2.trans (div_between_endpoints b hR hRp hpT).1⟩

theorem commonLower_error (a : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    commonLower a R T ≤ a/T+|a| *(1/R-1/T) := by
  have hT : 0 < T := hR.trans_le hRT
  have hd : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have he : a/R=a/T+a*(1/R-1/T) := by ring
  apply max_le
  · rw [he]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_abs_self a) hd)
  · exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg a) hd)

theorem commonUpper_error (b : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    b/T-|b| *(1/R-1/T) ≤ commonUpper b R T := by
  have hT : 0 < T := hR.trans_le hRT
  have hd : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have he : b/R=b/T+b*(1/R-1/T) := by ring
  apply le_min
  · rw [he]
    have h := mul_le_mul_of_nonneg_right (neg_abs_le b) hd
    nlinarith
  · exact sub_le_self _ (mul_nonneg (abs_nonneg b) hd)

theorem common_length_lower (a b : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    (b-a)/T-(|a|+|b|)*(1/R-1/T) ≤ commonUpper b R T-commonLower a R T := by
  have hl := commonLower_error a hR hRT
  have hu := commonUpper_error b hR hRT
  have he : (b-a)/T-(|a|+|b|)*(1/R-1/T) =
      (b/T-|b| *(1/R-1/T))-(a/T+|a| *(1/R-1/T)) := by ring
  rw [he]
  exact sub_le_sub hu hl

theorem common_height_bound (a b m : ℝ) {R T : ℝ} (hR : 0 < R)
    (hm : m ∈ Set.Ioc (commonLower a R T) (commonUpper b R T)) :
    |m| ≤ max |a| |b|/R := by
  apply abs_le.mpr
  constructor
  · have h1 : -(max |a| |b|) ≤ a :=
      (neg_le_neg (le_max_left _ _)).trans (neg_abs_le a)
    have h2 := div_le_div_of_nonneg_right h1 hR.le
    have h3 : a/R ≤ commonLower a R T := le_max_left _ _
    rw [neg_div] at h2
    exact h2.trans (h3.trans hm.1.le)
  · have h1 : b ≤ max |a| |b| := (le_abs_self b).trans (le_max_right _ _)
    have h2 := div_le_div_of_nonneg_right h1 hR.le
    exact hm.2.trans ((min_le_left _ _).trans h2)





theorem reciprocal_width_bound {R T epsilon : ℝ} (hR : 0 < R) (hRT : R ≤ T)
    (hwidth : T ≤ (1+epsilon)*R) : 1/R-1/T ≤ epsilon/T := by
  have hT : 0 < T := hR.trans_le hRT
  have hdiv : T/R ≤ 1+epsilon := (div_le_iff₀ hR).mpr hwidth
  have he : (1/R-1/T)*T=T/R-1 := by field_simp
  apply (le_div_iff₀ hT).mpr
  rw [he]
  linarith

theorem affine_common_interval (A D Y q m : ℝ) {R p T : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ p) (hpT : p ≤ T)
    (hm : m ∈ Set.Ioc (commonLower (-A/q) R T) (commonUpper ((D*Y-A)/q) R T)) :
    0 < A+p*q*m ∧ A+p*q*m ≤ D*Y := by
  have hp : 0 < p := hR.trans_le hRp
  have hc := common_interval_subset (-A/q) ((D*Y-A)/q) hR hRp hpT hm
  simp only [div_div] at hc
  have hl := (div_lt_iff₀ (mul_pos hq hp)).mp hc.1
  have hu := (le_div_iff₀ (mul_pos hq hp)).mp hc.2
  constructor <;> nlinarith

end ErdosCommonParameterInterval



namespace ErdosCommonMInterval
open ErdosCommonParameterInterval

theorem closed_subset (A D Y q R T : ℝ) :
    interval A D Y q R T ⊆
      Set.Ioc (commonLower (-A/q) R T) (commonUpper ((D*Y-A)/q) R T) := by
  intro m hm
  exact ⟨by have := hm.1; dsimp [interval,lower] at this <;> linarith, hm.2⟩

theorem closed_affine {A D Y q R T m p : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ p) (hpT : p ≤ T)
    (hm : m ∈ interval A D Y q R T) :
    0 < A+p*q*m ∧ A+p*q*m ≤ D*Y :=
  affine_common_interval A D Y q m hq hR hRp hpT (closed_subset A D Y q R T hm)

theorem integer_decode {A m : ℤ} {D Y q p : ℕ} {R T : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval A D Y q R T)
    (hdvd : (D : ℤ) ∣ A+(p : ℤ)*q*m) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ Y ∧ (D : ℤ)*n=A+(p : ℤ)*q*m := by
  have hb := closed_affine (by exact_mod_cast hq) hR hRp hpT hm
  obtain ⟨k,hk⟩ := hdvd
  have he : (A : ℝ)+(p : ℝ)*q*m=(D : ℝ)*(k : ℝ) := by exact_mod_cast hk
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hkpos : (0 : ℝ) < k := by nlinarith [hb.1]
  have hkY : (k : ℝ) ≤ Y := by nlinarith [hb.2]
  have hkint : 0 ≤ k := le_of_lt (by exact_mod_cast hkpos : (0 : ℤ) < k)
  refine ⟨k.toNat, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ k := by exact_mod_cast (by exact_mod_cast hkpos : (0 : ℤ) < k)
    exact_mod_cast (show (1 : ℤ) ≤ (k.toNat : ℤ) by simpa [Int.toNat_of_nonneg hkint] using this)
  · have : k ≤ (Y : ℤ) := by exact_mod_cast hkY
    exact_mod_cast (show (k.toNat : ℤ) ≤ (Y : ℤ) by simpa [Int.toNat_of_nonneg hkint] using this)
  · simpa [Int.toNat_of_nonneg hkint] using hk.symm

theorem decode_spec {A m : ℤ} {D Y q p : ℕ} {R T : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval A D Y q R T)
    (hdvd : (D : ℤ) ∣ A+(p : ℤ)*q*m) :
    1 ≤ decode A m D q p ∧ decode A m D q p ≤ Y ∧
      (D : ℤ)*decode A m D q p=A+(p : ℤ)*q*m := by
  obtain ⟨n,hn1,hnY,hn⟩ := integer_decode hD hq hR hRp hpT hm hdvd
  have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hid : decode A m D q p=n := by
    unfold decode
    rw [← hn,Int.mul_ediv_cancel_left _ hDn]
    simp
  simpa only [hid] using And.intro hn1 (And.intro hnY hn)

theorem reference_rpow {P Y R q : ℝ} (hP : 1 < P)
    (hY : 0 < Y) (hR : 0 < R) (hq : 0 < q) :
    P ^ lengthExponent P Y R q = referenceLength Y R q := by
  have hJ : 0 < referenceLength Y R q := div_pos hY (mul_pos hR hq)
  rw [lengthExponent,Real.rpow_def_of_pos (by linarith : 0 < P)]
  rw [mul_div_cancel₀ _ (Real.log_pos hP).ne']
  exact Real.exp_log hJ

end ErdosCommonMInterval



namespace ErdosCommonMInterval
open ErdosCommonParameterInterval

theorem endpoint_magnitude {A D Y q : ℝ} (hD : 0 ≤ D) (hY : 0 ≤ Y) (hq : 0 < q) :
    |-A/q|+|(D*Y-A)/q| ≤ (D*Y+2*|A|)/q := by
  rw [abs_div,abs_div,abs_of_pos hq,abs_neg,← add_div]
  apply div_le_div_of_nonneg_right _ hq.le
  have h : |D*Y-A| ≤ |D*Y|+|A| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (D*Y) 0 A
  rw [abs_of_nonneg (mul_nonneg hD hY)] at h
  linarith

theorem closed_length_lower {A D Y q R T H e : ℝ}
    (hD : 1 ≤ D) (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (hRT : R ≤ T)
    (hH : 0 ≤ H) (he : 0 ≤ e) (hwidth : T ≤ (1+e)*R) (hA : |A| ≤ Y*H) :
    (1-2*e*(1+H))*D*referenceLength Y R q-1 ≤
      upper A D Y q R T-lower A q R T := by
  have hT : 0 < T := hR.trans_le hRT
  have hD0 : 0 < D := by linarith
  have hd0 : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have hd := (reciprocal_width_bound hR hRT hwidth).trans
    (div_le_div_of_nonneg_left he hR hRT)
  have hmag := endpoint_magnitude (A := A) hD0.le hY.le hq
  have hbase : (D*Y-A)/q-(-A/q) = D*Y/q := by ring
  have hnorm : D*Y/q+|-A/q|+|(D*Y-A)/q| ≤ 2*D*Y*(1+H)/q := by
    have hDH : Y*H ≤ D*Y*H := by nlinarith [mul_nonneg hY.le hH]
    have : (D*Y+2*|A|)/q ≤ (D*Y+2*D*Y*H)/q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    calc
      _ ≤ D*Y/q+(D*Y+2*D*Y*H)/q := by linarith
      _ = _ := by ring
  have hnorm0 : 0 ≤ D*Y/q+|-A/q|+|(D*Y-A)/q| := by positivity
  have hprod := mul_le_mul hnorm hd hd0 (by positivity : 0 ≤ 2*D*Y*(1+H)/q)
  have hf := common_length_lower (-A/q) ((D*Y-A)/q) hR hRT
  rw [hbase] at hf
  have heq : (D*Y/q)/T-(|-A/q|+|(D*Y-A)/q|)*(1/R-1/T) =
      D*Y/(R*q)-(D*Y/q+|-A/q|+|(D*Y-A)/q|)*(1/R-1/T) := by ring
  rw [heq] at hf
  dsimp [upper,lower,referenceLength]
  have heq2 : D*Y/(R*q)-(2*D*Y*(1+H)/q)*(e/R) =
      (1-2*e*(1+H))*D*(Y/(R*q)) := by ring
  linarith

theorem closed_length_upper (A D Y q R T : ℝ) :
    upper A D Y q R T-lower A q R T ≤ D*referenceLength Y R q-1 := by
  have hU : upper A D Y q R T ≤ ((D*Y-A)/q)/R := min_le_left _ _
  have hL : (-A/q)/R+1 ≤ lower A q R T := by
    have h : (-A/q)/R ≤ ErdosCommonParameterInterval.commonLower (-A/q) R T := le_max_left _ _
    dsimp [lower] <;> linarith
  have heq : ((D*Y-A)/q)/R-((-A/q)/R+1)=D*referenceLength Y R q-1 := by
    dsimp [referenceLength] <;> ring
  linarith

theorem closed_height {A D Y q R T H m : ℝ}
    (hD : 0 ≤ D) (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R)
    (hA : |A| ≤ Y*H) (hm : m ∈ interval A D Y q R T) :
    |m| ≤ (D+H)*referenceLength Y R q := by
  have hb := common_height_bound (-A/q) ((D*Y-A)/q) m hR
    (closed_subset A D Y q R T hm)
  have ha : |-A/q| ≤ (D*Y+Y*H)/q := by
    rw [abs_div,abs_neg,abs_of_pos hq]
    exact div_le_div_of_nonneg_right (by nlinarith) hq.le
  have hc : |(D*Y-A)/q| ≤ (D*Y+Y*H)/q := by
    rw [abs_div,abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ hq.le
    have h : |D*Y-A| ≤ |D*Y|+|A| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (D*Y) 0 A
    rw [abs_of_nonneg (mul_nonneg hD hY.le)] at h
    linarith
  calc
    _ ≤ max |-A/q| |(D*Y-A)/q|/R := hb
    _ ≤ ((D*Y+Y*H)/q)/R := div_le_div_of_nonneg_right (max_le ha hc) hR.le
    _ = _ := by dsimp [referenceLength] <;> ring

end ErdosCommonMInterval


section

open _root_.Filter
open scoped Topology
namespace ErdosCommonMInterval

theorem eventual_polynomial_cutoff (B K : ℝ) (hB : 0 ≤ B) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 2 ≤ w ∧ w^B ≤ Real.exp (K*(Real.log w)^3) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (B/K))] with w hw hL
  have hw0 : 0 < w := by linarith
  have hL1 : 1 ≤ Real.log w := (le_max_left _ _).trans hL
  have hBL : B ≤ K*Real.log w := by
    have := (div_le_iff₀ hK).mp (show B/K ≤ Real.log w from (le_max_right _ _).trans hL)
    nlinarith
  refine ⟨hw, ?_⟩
  rw [Real.rpow_def_of_pos hw0]
  apply Real.exp_le_exp.mpr
  have hsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hpow : (Real.log w)^2 ≤ (Real.log w)^3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hBL (by linarith : 0 ≤ Real.log w)]

theorem subbin_loss {w C : ℝ} (hw : 1 ≤ w) (hC : 0 ≤ C) :
    2*w^(-2*C-10)*(1+w^(C+2)) ≤ 4*w^(-8 : ℝ) := by
  have hw0 : 0 < w := by linarith
  have hH : 1 ≤ w^(C+2) := Real.one_le_rpow hw (by linarith)
  have hmul : w^(-2*C-10)*w^(C+2) = w^(-C-8) := by
    rw [← Real.rpow_add hw0];congr 1;ring
  have hcmp : w^(-C-8) ≤ w^(-8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have hnon : 0 ≤ w^(-2*C-10) := Real.rpow_nonneg hw0.le _
  have hle : w^(-2*C-10) ≤ w^(-2*C-10)*w^(C+2) := by nlinarith
  nlinarith

theorem height_absorption {w P C : ℝ} (hw : 2 ≤ w)
    (hP : w^(50*(C+3)) ≤ P) : 2*w^(C+2) ≤ P^((2 : ℝ)/100) := by
  have hw0 : 0 < w := by linarith
  have h1 : 2*w^(C+2) ≤ w^(C+3) := by
    have he : w^(C+3)=w*w^(C+2) := by
      calc w^(C+3) = w^((1 : ℝ)+(C+2)) := by congr 1;ring
           _ = w*w^(C+2) := by rw [Real.rpow_add hw0,Real.rpow_one]
    rw [he]
    exact mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hw0.le _)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hw0.le (50*(C+3))) hP
    (by norm_num : (0 : ℝ) ≤ 2/100)
  have he : (w^(50*(C+3)))^((2 : ℝ)/100)=w^(C+3) := by
    rw [← Real.rpow_mul hw0.le];congr 1;ring
  exact h1.trans (by rwa [he] at h2)

theorem relativeError_tends_zero : Tendsto relativeError atTop (𝓝 0) := by
  have h8 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8)
  have h2 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)
  change Tendsto (fun w : ℝ => 4*w^(-8 : ℝ)+w^(-2 : ℝ)) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using (h8.const_mul 4).add h2

theorem uniform_common_interval (C K delta : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∃ W : ℝ, ∀ w : ℝ, W ≤ w → ∀ P A D Y q R T : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P →
      1 ≤ D → D ≤ w^C → 0 < Y → 0 < q → 0 < R → R ≤ T →
      T ≤ (1+w^(-2*C-10))*R → |A| ≤ Y*w^(C+2) →
      2 ≤ lengthExponent P Y R q →
      (1-delta)*D*referenceLength Y R q ≤ upper A D Y q R T-lower A q R T ∧
      upper A D Y q R T-lower A q R T ≤ D*referenceLength Y R q ∧
      (interval A D Y q R T).Nonempty ∧
      ∀ m ∈ interval A D Y q R T, |m| ≤ P^(lengthExponent P Y R q+(2 : ℝ)/100) := by
  have hE := relativeError_tends_zero.eventually (gt_mem_nhds hd0)
  have hpoly := eventual_polynomial_cutoff (50*(C+3)) K (by positivity) hK
  obtain ⟨W,hW⟩ := eventually_atTop.mp (hE.and hpoly)
  refine ⟨W, ?_⟩
  intro w hw P A D Y q R T hP hD hDu hY hq hR hRT hwidth hA hs
  obtain ⟨hErr,hw2,hpow⟩ := hW w hw
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hwpow : w ≤ w^(50*(C+3)) := by
    calc w = w^(1 : ℝ) := (Real.rpow_one _).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hw1 (by nlinarith)
  have hwP : w ≤ P := hwpow.trans (hpow.trans hP)
  have hP1 : 1 < P := by linarith
  have hD0 : 0 < D := by linarith
  have hJ : 0 < referenceLength Y R q := div_pos hY (mul_pos hR hq)
  have hJid := reference_rpow hP1 hY hR hq
  have hJlow : P^2 ≤ referenceLength Y R q := by
    rw [← hJid]
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hP1.le hs
  have hJw : w^2 ≤ referenceLength Y R q := by nlinarith
  have hpay : 1 ≤ w^(-2 : ℝ)*D*referenceLength Y R q := by
    have hid : w^(-2 : ℝ)*w^2=1 := by
      rw [← Real.rpow_ofNat,← Real.rpow_add hw0];norm_num
    have hn : 0 ≤ w^(-2 : ℝ) := Real.rpow_nonneg hw0.le _
    have hm : w^2 ≤ D*referenceLength Y R q := by nlinarith
    have := mul_le_mul_of_nonneg_left hm hn
    nlinarith
  have hraw := closed_length_lower hD hY hq hR hRT
    (Real.rpow_nonneg hw0.le (C+2)) (Real.rpow_nonneg hw0.le (-2*C-10)) hwidth hA
  have hcost := subbin_loss hw1 hC
  have hlen : (1-delta)*D*referenceLength Y R q ≤
      upper A D Y q R T-lower A q R T := by
    have hmul := mul_le_mul_of_nonneg_right hcost (mul_pos hD0 hJ).le
    have herrmul := mul_le_mul_of_nonneg_right hErr.le (mul_pos hD0 hJ).le
    dsimp [relativeError] at herrmul
    nlinarith
  refine ⟨hlen, (closed_length_upper A D Y q R T).trans (by linarith), ?_, ?_⟩
  · apply Set.nonempty_Icc.mpr
    have := mul_pos (mul_pos (by linarith : 0 < 1-delta) hD0) hJ
    linarith
  · intro m hm
    have hheight := closed_height hD0.le hY hq hR hA hm
    have hDC : D ≤ w^(C+2) := hDu.trans
      (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith))
    have habs := height_absorption hw2 (hpow.trans hP)
    have hp02 : D+w^(C+2) ≤ P^((2 : ℝ)/100) := by linarith
    calc
      |m| ≤ (D+w^(C+2))*referenceLength Y R q := hheight
      _ ≤ P^((2 : ℝ)/100)*referenceLength Y R q := mul_le_mul_of_nonneg_right hp02 hJ.le
      _ = P^(lengthExponent P Y R q+(2 : ℝ)/100) := by
        rw [← hJid,← Real.rpow_add (by linarith : 0 < P)];congr 1;ring

theorem uniform_integer_common_interval (C K delta : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∃ W : ℝ, ∀ w : ℝ, W ≤ w → ∀ P R T : ℝ, ∀ A : ℤ, ∀ D Y q : ℕ,
      Real.exp (K*(Real.log w)^3) ≤ P →
      0 < D → (D : ℝ) ≤ w^C → 0 < Y → 0 < q → 0 < R → R ≤ T →
      T ≤ (1+w^(-2*C-10))*R → |(A : ℝ)| ≤ (Y : ℝ)*w^(C+2) →
      2 ≤ lengthExponent P Y R q →
      (1-delta)*(D : ℝ)*referenceLength Y R q ≤ upper A D Y q R T-lower A q R T ∧
      upper A D Y q R T-lower A q R T ≤ (D : ℝ)*referenceLength Y R q ∧
      (interval A D Y q R T).Nonempty ∧
      (∀ m ∈ interval A D Y q R T, |m| ≤ P^(lengthExponent P Y R q+(2 : ℝ)/100)) ∧
      ∀ p : ℕ, ∀ m : ℤ, R ≤ (p : ℝ) → (p : ℝ) ≤ T →
        (m : ℝ) ∈ interval A D Y q R T → (D : ℤ) ∣ A+(p : ℤ)*q*m →
        1 ≤ decode A m D q p ∧ decode A m D q p ≤ Y ∧
          (D : ℤ)*decode A m D q p=A+(p : ℤ)*q*m := by
  obtain ⟨W,hW⟩ := uniform_common_interval C K delta hC hK hd0 hd1
  refine ⟨W, ?_⟩
  intro w hw P R T A D Y q hP hD hDu hY hq hR hRT hwidth hA hs
  have hb := hW w hw P A D Y q R T hP
    (by exact_mod_cast (show 1 ≤ D from hD)) hDu
    (by exact_mod_cast hY) (by exact_mod_cast hq) hR hRT hwidth hA hs
  refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
  intro p m hRp hpT hm hdvd
  exact decode_spec hD hq hR hRp hpT hm hdvd

end ErdosCommonMInterval

end



namespace ErdosStoppedArithmetic
open ErdosCommonMInterval ErdosAlignedProgression

theorem common_slice_mem_parameter (Y q p : ℕ) (r : ℚ) (R T : ℝ) (m : ℤ)
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval r.num r.den Y q R T)
    (hdiv : (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m) :
    m ∈ parameterInterval Y r (p*q) := by
  have hp : 0 < p := by exact_mod_cast hR.trans_le hRp
  have hdiv' : (r.den : ℤ) ∣ r.num+(p : ℤ)*q*m := by
    simpa only [Nat.cast_mul] using hdiv
  obtain ⟨n,hn,hY,he⟩ := integer_decode r.den_pos hq hR hRp hpT hm hdiv'
  apply (mem_parameterInterval Y r (p*q) (Nat.mul_pos hp hq) m).mpr
  have hD : (0 : ℤ) ≤ r.den := Int.natCast_nonneg _
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hY' : (n : ℤ) ≤ Y := by exact_mod_cast hY
  have hlo := mul_le_mul_of_nonneg_left hn' hD
  have hhi := mul_le_mul_of_nonneg_left hY' hD
  simp only [mul_one,he] at hlo hhi
  simpa only [Nat.cast_mul] using And.intro hlo hhi

theorem common_slice_endpoint_height (w Cs P R T : ℝ) (A : ℤ) (D Y q : ℕ)
    (hw : 1 ≤ w) (hP : 1 < P) (hDw : (D : ℝ) ≤ w^Cs)
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R)
    (hA : |(A : ℝ)| ≤ (Y : ℝ)*w^(Cs+2))
    (hne : (interval A D Y q R T).Nonempty) :
    max |lower A q R T| |upper A D Y q R T| ≤
      2*w^(Cs+2)*P^(lengthExponent P Y R q) := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hEnds : lower A q R T ≤ upper A D Y q R T := Set.nonempty_Icc.mp hne
  have hLo := closed_height hD' hY' hq' hR hA
    (show lower A q R T ∈ interval A D Y q R T from ⟨le_rfl,hEnds⟩)
  have hHi := closed_height hD' hY' hq' hR hA
    (show upper A D Y q R T ∈ interval A D Y q R T from ⟨hEnds,le_rfl⟩)
  have hDC : (D : ℝ) ≤ w^(Cs+2) := hDw.trans
    (Real.rpow_le_rpow_of_exponent_le hw (by linarith))
  have hJ : 0 ≤ referenceLength Y R q := (div_pos hY' (mul_pos hR hq')).le
  have hBound := mul_le_mul_of_nonneg_right
    (show (D : ℝ)+w^(Cs+2) ≤ 2*w^(Cs+2) by linarith) hJ
  rw [reference_rpow hP hY' hR hq']
  exact (max_le hLo hHi).trans (by simpa only [mul_assoc] using hBound)

end ErdosStoppedArithmetic


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

theorem smallEuler_eq_primeProduct (w : ℝ) :
    SmallSieveFinite.smallEuler ⌊w⌋₊ = primeProduct w := by
  unfold SmallSieveFinite.smallEuler primeProduct
  rw [cutoffPrimes_eq_filtered_Ioc]
  simp only [one_div]

open _root_.Filter
open scoped Topology

end ErdosInverseEuler

end

section

namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosInverseCounts ErdosInverseEuler
  ErdosPrimeInputs.MertensStrong ReferenceProductsBasics
attribute [local instance] Classical.propDecidable

theorem smallEuler_nat_primeProduct (P : ℕ) :
    SmallSieveFinite.smallEuler P=primeProduct (P : ℝ) := by
  simpa only [Nat.floor_natCast] using smallEuler_eq_primeProduct (P : ℝ)

theorem smallEuler_prime_step (P : ℕ) (hP : P.Prime) :
    SmallSieveFinite.smallEuler P=(1-(P : ℝ)⁻¹)*SmallSieveFinite.smallEuler (P-1) := by
  have hset : LargePrimeDeletion.cutoffPrimes P = insert P (LargePrimeDeletion.cutoffPrimes (P-1)) := by
    ext p
    simp only [LargePrimeDeletion.mem_cutoffPrimes,Finset.mem_insert]
    constructor
    · rintro ⟨hp,hpP⟩
      by_cases he : p=P
      · exact Or.inl he
      · exact Or.inr ⟨hp,by omega⟩
    · rintro (rfl | ⟨hp,hpP⟩)
      · exact ⟨hP,le_rfl⟩
      · exact ⟨hp,by omega⟩
  have hnot : P ∉ LargePrimeDeletion.cutoffPrimes (P-1) := by
    rw [LargePrimeDeletion.mem_cutoffPrimes]
    have hp := hP.pos
    omega
  unfold SmallSieveFinite.smallEuler
  rw [hset,Finset.prod_insert hnot]

theorem smallEuler_strict_le_two_closed (P : ℕ) (hP : P.Prime) :
    SmallSieveFinite.smallEuler (P-1) ≤ 2*primeProduct (P : ℝ) := by
  have hV : 0 ≤ SmallSieveFinite.smallEuler (P-1) := by
    rw [smallEuler_nat_primeProduct]
    exact (actual_primeProduct_pos _).le
  have hp : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have h2 : (2 : ℝ) ≤ P := by exact_mod_cast hP.two_le
  have hinv : (P : ℝ)⁻¹ ≤ 1/2 := by rw [← one_div];exact (div_le_iff₀ hp).mpr (by linarith)
  have hfactor := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-(P : ℝ)⁻¹ by linarith) hV
  rw [← smallEuler_nat_primeProduct P,smallEuler_prime_step P hP]
  nlinarith

theorem original_individual_upper_closed :
    ∃ C : ℝ,0 < C ∧ ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P.Prime → P0 ≤ P →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ t ∈ d.primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(d : ℝ) →
        (modulusCount Y (LargePrimeDeletion.cutoffPrimes (P-1)) a d : ℝ) ≤
          C*((Y : ℝ)/(d : ℝ))*primeProduct (P : ℝ) := by
  obtain ⟨C,hC,P0,hP0,hUpper⟩ := original_individual_upper
  refine ⟨2*C,by positivity,P0,hP0,?_⟩
  intro P hPrime hP Y d a hY hd hlarge hJ
  have hU := hUpper P hP Y d a hY hd hlarge hJ
  have hE := smallEuler_strict_le_two_closed P hPrime
  have hm := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ C*((Y : ℝ)/(d : ℝ)) by positivity)
  calc
    _ ≤ C*((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler (P-1) := hU
    _ ≤ C*((Y : ℝ)/(d : ℝ))*(2*primeProduct (P : ℝ)) := hm
    _ = _ := by ring

end ErdosStoppedArithmetic

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagPairBinding
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosUnitLifts
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem actual_tag_original_tests (P : ℝ) (r : ℚ) (q p : ℕ) (a : ℕ → ℕ) (m : ℤ)
    (h : actualTagGood P r q a p m) :
    (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m ∧
      ∀ t ∈ smallPrimeSet P,
        ¬Int.ModEq (t : ℤ) ((r.num+((p*q : ℕ) : ℤ)*m)/(r.den : ℤ)) (a t : ℤ) := by
  have he : r.num+((p*q : ℕ) : ℤ)*m = r.num+(q : ℤ)*m*p := by push_cast <;> ring
  rw [he]
  refine ⟨h.1,?_⟩
  intro t ht hh
  exact h.2 t ht ((ZMod.intCast_eq_intCast_iff _ _ t).mpr hh)

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HypotheticalSubbinLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosCommonMInterval ErdosAlignedProgression
  ErdosInverseAlignment ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem hypothetical_subbin_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P R V : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      203/100 ≤ lengthExponent P Y R q → lengthExponent P Y R q ≤ 219/100 →
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (∀ p ∈ intervalPrimes R V 1 0,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p →
          aligns (fun u => (a u : ℤ)) r t) →
      (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*referenceLength Y R q*primeProduct P ≤
        ∑ p : intervalPrimes R V 1 0,
          hypotheticalRowCount Y (smallPrimeSet P) (intervalPrimes R V 1 0) a r q
            (subbin_primality R V) p := by
  obtain ⟨K,hK,hPairs⟩ := moving_subbin_actual_pair_lower_jb247 Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wA,hwA,hA⟩ := hPairs rho xi hrho hxi
  obtain ⟨wC,hC⟩ := uniform_integer_common_interval Cs K (1/1000) hCs hK (by norm_num) (by norm_num)
  refine ⟨max wA wC,hwA.trans (le_max_left _ _),?_⟩
  intro w hw P R V hPl hPu hR hVlo hVhi Y q hY hq r a hDen hNum hs hsU hqSmall hGeometry
  have hw4 : 4 ≤ w := hwA.trans ((le_max_left _ _).trans hw)
  have hw1 : 1 < w := by linarith
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hRatio : 0 < V/R := (div_pos hxi (by positivity)).trans_le hVlo
  have hV : 0 < V := (div_pos_iff.mp hRatio).resolve_right (by intro h;linarith [h.2]) |>.1
  have hWidth : R+V ≤ (1+w^(-2*Cs-10))*R := by
    have hh := (div_le_iff₀ hR0).mp hVhi
    rw [show -(2*Cs+10)= -2*Cs-10 by ring] at hh
    nlinarith
  have hP1 : 1 < P := by
    have he : 1 < Real.exp (K*(Real.log w)^3) := Real.one_lt_exp_iff.mpr
      (mul_pos hK (pow_pos (Real.log_pos hw1) _))
    exact he.trans_le hPl
  have hb := hC w ((le_max_right _ _).trans hw) P R (R+V) r.num r.den Y q hPl
    r.den_pos hDen hY hq hR0 (by linarith) hWidth hNum (by linarith)
  have hJid := reference_rpow hP1 (show (0 : ℝ) < Y by exact_mod_cast hY) hR0
    (show (0 : ℝ) < q by exact_mod_cast hq)
  have hLength : (999/1000 : ℝ)*(r.den : ℝ)*P^(lengthExponent P Y R q) ≤
      upper r.num r.den Y q R (R+V)-lower r.num q R (R+V) := by
    rw [hJid]
    convert hb.1 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hHeight := common_slice_endpoint_height w Cs P R (R+V) r.num r.den Y q
    hw1.le hP1 hDen hY hq hR0 hNum hb.2.2.1
  have hPair := hA w ((le_max_left _ _).trans hw) P (lengthExponent P Y R q)
    (lower r.num q R (R+V)) (upper r.num r.den Y q R (R+V)) R V hPl hPu
    hs hsU hR hVlo hVhi r hDen q a hqSmall hLength hHeight
  rw [hJid] at hPair
  apply hPair.trans
  apply pair_count_le_hypothetical_sum Y (smallPrimeSet P) (intervalPrimes R V 1 0) a r q
    (subbin_primality R V) _ (actualTagGood P r q a) hGeometry
  · intro p hp m hm hGood
    obtain ⟨d,_hd,hm⟩ := Finset.mem_biUnion.mp hm
    have hEnds := (mem_primeMultiplesIn d P _ _ m).mp hm
    have hpBounds := (mem_intervalPrimes R V 1 0 p).mp hp
    exact common_slice_mem_parameter Y q p r R (R+V) m hq hR0 hpBounds.2.1.le
      hpBounds.2.2.1 ⟨hEnds.1.le,hEnds.2.1.le⟩
      (actual_tag_original_tests P r q p a m hGood).1
  · intro p _hp m _hm hGood
    exact actual_tag_original_tests P r q p a m hGood

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SubbinAggregation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedSubbinAggregation
open ErdosTagSubbins ErdosInversePrimeBin Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem subbin_eq_intervalPrimes {R theta : ℝ} {N i : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) :
    subbin R theta N i = intervalPrimes (left R theta N i) (step R theta N) 1 0 := by
  ext p
  rw [mem_subbin hR ht hN,mem_intervalPrimes,right_eq_left_add]
  simp [Int.ModEq]

theorem aggregate_subbin_lower {R theta c V : ℝ} {N : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (reward weight : ℕ → ℝ) (localWeight : Fin N → ℝ)
    (hweight : ∀ i : Fin N,∀ p ∈ subbin R theta N i,weight p ≤ localWeight i)
    (hlower : ∀ i : Fin N,
      c*((subbin R theta N i).card : ℝ)*localWeight i*V ≤
        ∑ p ∈ subbin R theta N i,reward p) :
    c*V*(∑ p ∈ primeBin R theta,weight p) ≤ ∑ p ∈ primeBin R theta,reward p := by
  rw [sum_partition hR ht hN weight,sum_partition hR ht hN reward,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have hsum : (∑ p ∈ subbin R theta N i,weight p) ≤
      ((subbin R theta N i).card : ℝ)*localWeight i := by
    calc
      _ ≤ ∑ _p ∈ subbin R theta N i,localWeight i := Finset.sum_le_sum (hweight i)
      _ = _ := by simp
  calc
    _ ≤ c*V*(((subbin R theta N i).card : ℝ)*localWeight i) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hc hV)
    _ = c*((subbin R theta N i).card : ℝ)*localWeight i*V := by ring
    _ ≤ _ := hlower i

theorem reference_length_le {Y q R p : ℝ} (hY : 0 ≤ Y) (hq : 0 < q)
    (hR : 0 < R) (hp : R ≤ p) : Y/(p*q) ≤ Y/(R*q) :=
  div_le_div_of_nonneg_left hY (mul_pos hR hq) (mul_le_mul_of_nonneg_right hp hq.le)

theorem aggregate_reference_lower {R theta Y q V : ℝ} {N : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N)
    (hY : 0 ≤ Y) (hq : 0 < q) (hV : 0 ≤ V) (reward : ℕ → ℝ)
    (hlower : ∀ i : Fin N,
      (39/100 : ℝ)*((subbin R theta N i).card : ℝ)*(Y/(left R theta N i*q))*V ≤
        ∑ p ∈ subbin R theta N i,reward p) :
    (39/100 : ℝ)*V*(∑ p ∈ primeBin R theta,Y/((p : ℝ)*q)) ≤
      ∑ p ∈ primeBin R theta,reward p := by
  apply aggregate_subbin_lower hR ht hN (by norm_num) hV reward
    (fun p => Y/((p : ℝ)*q)) (fun i => Y/(left R theta N i*q)) _ hlower
  intro i p hp
  exact reference_length_le hY hq (left_pos hR ht hN) ((mem_subbin hR ht hN).mp hp).2.1.le

end ErdosStoppedSubbinAggregation


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SubbinScaleInheritance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedSubbinAggregation
open ErdosTagSubbins ErdosInversePrimeBin

theorem subbin_scale_inheritance {R theta w Cs xi lowerBound : ℝ}
    (hw : 1 < w) (hCs : 0 ≤ Cs) (hR : 0 < R)
    (hxi : 0 < xi) (htxi : xi/4 ≤ theta) (ht1 : theta ≤ 1)
    (hLower : lowerBound ≤ R) (i : Fin (count w Cs)) :
    0 < left R theta (count w Cs) i ∧ 0 < step R theta (count w Cs) ∧
      lowerBound ≤ left R theta (count w Cs) i ∧
      left R theta (count w Cs) i ≤ (1+theta)*R ∧
      xi/(16*w^(2*Cs+10)) ≤ step R theta (count w Cs)/left R theta (count w Cs) i ∧
      step R theta (count w Cs)/left R theta (count w Cs) i ≤ w^(-(2*Cs+10)) ∧
      left R theta (count w Cs) i + step R theta (count w Cs) ≤ (1+theta)*R := by
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le htxi
  have hN : 0 < count w Cs := (count_bounds hw hCs).1
  refine ⟨left_pos hR ht hN,step_pos hR ht hN,
    hLower.trans (left_lower (step_pos hR ht hN).le),
    (left_lt_right hR ht hN).le.trans (right_upper hR ht i.isLt),
    width_lower hR hxi htxi ht1 hw hCs i.isLt,?_,?_⟩
  · simpa only [width,show -2*Cs-10=-(2*Cs+10) by ring] using
      (width_upper (i:=i) hR ht ht1 hw hCs)
  · rw [← right_eq_left_add]
    exact right_upper hR ht i.isLt

theorem subbin_inherits_band {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (band : ℝ → Prop)
    (hband : ∀ x ∈ Set.Icc R ((1+theta)*R),band x) (i : Fin N) :
    band (left R theta N i) := by
  apply hband
  exact ⟨left_lower (step_pos hR ht hN).le,
    (left_lt_right hR ht hN).le.trans (right_upper hR ht i.isLt)⟩

end ErdosStoppedSubbinAggregation


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

theorem primeHypothetical_on_prime (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) (hp : p.Prime) :
    primeHypothetical Y small a r q p =
      (modulusCount Y small (@hypotheticalClass a r p ⟨hp.ne_zero⟩) (p*q) : ℝ) := by
  simp only [primeHypothetical,dite_eq_left hp]

theorem primeHypothetical_row (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T) :
    primeHypothetical Y small a r q p.val=hypotheticalRowCount Y small T a r q hT p := by
  exact primeHypothetical_on_prime Y small a r q p.val (hT p.val p.property)

theorem primeHypothetical_sum (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) :
    (∑ p ∈ T,primeHypothetical Y small a r q p)=
      ∑ p : T,hypotheticalRowCount Y small T a r q hT p := by
  rw [← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl (fun p _ => primeHypothetical_row Y small T a r q hT p)

theorem primeHypothetical_agrees (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) (hp : p.Prime) (ha : aligns (fun t => (a t : ℤ)) r p) :
    primeHypothetical Y small a r q p=(modulusCount Y small a (p*q) : ℝ) := by
  rw [primeHypothetical_on_prime Y small a r q p hp]
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [hypothetical_count_agrees Y small a r (p*q) p hp ha]

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

theorem primeHypothetical_uniform_upper :
    ∃ C eta0 : ℝ,0 < C ∧ 0 < eta0 ∧ eta0 ≤ 1/4 ∧ 2*C*eta0 ≤ 1/20 ∧
      ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P.Prime → P0 ≤ P →
        ∀ Y q p : ℕ,∀ r : ℚ,∀ a : ℕ → ℕ,
        0 < Y → p.Prime → Squarefree (p*q) →
        (∀ t ∈ (p*q).primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(p*q : ℕ) →
        primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q p ≤
          C*((Y : ℝ)/(p*q : ℕ))*primeProduct (P : ℝ) := by
  obtain ⟨C,hC,P0,hP0,hUpper⟩ := original_individual_upper_closed
  refine ⟨C,min (1/4) (1/(40*C)),hC,lt_min (by norm_num) (by positivity),
    min_le_left _ _,?_,P0,hP0,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (min_le_right (1/4 : ℝ) (1/(40*C)))
      (show 0 ≤ 2*C by positivity)
    have he : 2*C*(1/(40*C))=(1/20 : ℝ) := by field_simp <;> ring
    exact hh.trans_eq he
  · intro P hPrime hP Y q p r a hY hp hsf hlarge hJ
    rw [primeHypothetical_on_prime Y _ a r q p hp,strict_smallPrimeSet_nat]
    exact hUpper P hPrime hP Y (p*q) _ hY hsf hlarge hJ

end ErdosStoppedArithmetic



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FullHypotheticalBinLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin
  ErdosPrimeInputs.MertensStrong ErdosTagSubbins ErdosStoppedSubbinAggregation
  NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable

theorem hypothetical_full_bin_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P R theta : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p →
          aligns (fun u => (a u : ℤ)) r t) →
      (39/100 : ℝ)*primeProduct P*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
        ∑ p ∈ primeBin R theta,primeHypothetical Y (smallPrimeSet P) a r q p := by
  obtain ⟨K,hK,hSub⟩ := hypothetical_subbin_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨w0,hw0,hS⟩ := hSub rho xi hrho hxi
  refine ⟨w0,hw0,?_⟩
  intro w hw P R theta hPl hPu hR hThetaLo hThetaHi Y q hY hq r a hDen hNum hBand hqSmall hGeometry
  have hw1 : 1 < w := by linarith [hw0.trans hw]
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le hThetaLo
  have hN : 0 < count w Cs := (count_bounds hw1 hCs).1
  apply aggregate_reference_lower (N:=count w Cs) hR0 ht hN (Nat.cast_nonneg Y)
    (show (0 : ℝ) < q by exact_mod_cast hq) (actual_primeProduct_pos P).le
    (primeHypothetical Y (smallPrimeSet P) a r q)
  intro i
  obtain ⟨_hLeft,_hStep,hRSub,_hLeftHi,hVlo,hVhi,_hRight⟩ :=
    subbin_scale_inheritance hw1 hCs hR0 hxi hThetaLo hThetaHi hR i
  have hBandSub := subbin_inherits_band hR0 ht hN
    (fun x => 203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) hBand i
  have hGeomSub : ∀ p ∈ intervalPrimes (left R theta (count w Cs) i)
      (step R theta (count w Cs)) 1 0,Squarefree (p*q) ∧ r.den.Coprime p ∧
      p ∉ smallPrimeSet P ∧ ∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t := by
    intro p hp
    have hpSub : p ∈ subbin R theta (count w Cs) i := by
      rwa [subbin_eq_intervalPrimes hR0 ht hN]
    exact hGeometry p (subbin_subset hR0 ht i.isLt hpSub)
  have hh := hS w hw P (left R theta (count w Cs) i) (step R theta (count w Cs))
    hPl hPu hRSub hVlo hVhi Y q hY hq r a hDen hNum hBandSub.1 hBandSub.2 hqSmall hGeomSub
  rw [← primeHypothetical_sum] at hh
  rw [subbin_eq_intervalPrimes hR0 ht hN]
  exact hh

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_OriginalBinWeightRange
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedArithmetic
open ErdosInversePrimeBin ErdosStoppedSubbinAggregation


theorem original_bin_weight_range (Y q R theta : ℝ) (hY : 0 ≤ Y) (hq : 0 < q)
    (hR : 0 < R) (ht : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ Y/(((1+theta)*R)*q) ∧ ∀ p ∈ primeBin R theta,
      Y/(((1+theta)*R)*q) ≤ Y/((p : ℝ)*q) ∧
      Y/((p : ℝ)*q) ≤ 2*(Y/(((1+theta)*R)*q)) := by
  have hDen : 0 < ((1+theta)*R)*q := by positivity
  have hDen0 : 0 < R*q := mul_pos hR hq
  have hDenBound : ((1+theta)*R)*q ≤ 2*(R*q) := by
    have hh := mul_le_mul_of_nonneg_right (show 1+theta ≤ (2 : ℝ) by linarith) hDen0.le
    nlinarith only [hh]
  refine ⟨div_nonneg hY hDen.le,?_⟩
  intro p hp
  obtain ⟨_hp,hlo,hhi⟩ := (mem_primeBin hR.le ht p).mp hp
  refine ⟨reference_length_le hY hq (hR.trans hlo) hhi,?_⟩
  calc
    Y/((p : ℝ)*q) ≤ Y/(R*q) := reference_length_le hY hq hR hlo.le
    _ ≤ (2*Y)/(((1+theta)*R)*q) := by
      apply (div_le_div_iff₀ hDen0 hDen).mpr
      have hh := mul_le_mul_of_nonneg_left hDenBound hY
      nlinarith only [hh]
    _ = _ := by ring

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualOwnerLocalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem missing_weight_bound {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w : α → ℝ) (lo eta : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo) :
    (∑ p ∈ P \ G,w p) ≤ 2*eta*(∑ p ∈ P,w p) := by
  have hcards : ((P \ G).card : ℝ)+(G.card : ℝ)=(P.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hGP
  have hmissing : ((P \ G).card : ℝ) ≤ eta*(P.card : ℝ) := by nlinarith
  have hsumlo : (P.card : ℝ)*lo ≤ ∑ p ∈ P,w p := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun p hp => (hW p hp).1)
  calc
    _ ≤ ∑ _p ∈ P \ G,2*lo := Finset.sum_le_sum (fun p hp => (hW p (Finset.mem_sdiff.mp hp).1).2)
    _ = ((P \ G).card : ℝ)*(2*lo) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (eta*(P.card : ℝ))*(2*lo) := mul_le_mul_of_nonneg_right hmissing (by positivity)
    _ = 2*eta*((P.card : ℝ)*lo) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumlo (by positivity)

theorem near_full_owner_lower {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w T : α → ℝ) (lo eta C V : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo)
    (hAll : (39/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ P,T p)
    (hUpper : ∀ p ∈ P,T p ≤ C*V*w p) (hBudget : 2*C*eta ≤ (1/20 : ℝ)) :
    (34/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ G,T p := by
  have hw0 (p : α) (hp : p ∈ P) : 0 ≤ w p := hlo.trans (hW p hp).1
  have hsum0 : 0 ≤ ∑ p ∈ P,w p := Finset.sum_nonneg hw0
  have hmiss := missing_weight_bound P G hGP w lo eta hlo heta hNear hW
  have hmissT : (∑ p ∈ P \ G,T p) ≤ (1/20 : ℝ)*V*(∑ p ∈ P,w p) := by
    calc
      _ ≤ ∑ p ∈ P \ G,C*V*w p := Finset.sum_le_sum (fun p hp => hUpper p (Finset.mem_sdiff.mp hp).1)
      _ = C*V*(∑ p ∈ P \ G,w p) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*V*(2*eta*(∑ p ∈ P,w p)) := mul_le_mul_of_nonneg_left hmiss (mul_nonneg hC hV)
      _ = (2*C*eta)*(V*(∑ p ∈ P,w p)) := by ring
      _ ≤ (1/20 : ℝ)*(V*(∑ p ∈ P,w p)) := mul_le_mul_of_nonneg_right hBudget (mul_nonneg hV hsum0)
      _ = _ := by ring
  have hsplit : (∑ p ∈ P \ G,T p)+(∑ p ∈ G,T p)=∑ p ∈ P,T p := Finset.sum_sdiff hGP
  nlinarith

theorem near_full_owner_comparison {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w T reference : α → ℝ) (lo eta C V : ℝ)
    (hlo : 0 ≤ lo) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo)
    (hAll : (39/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ P,T p)
    (hUpper : ∀ p ∈ P,T p ≤ C*V*w p) (hBudget : 2*C*eta ≤ (1/20 : ℝ))
    (hReference : ∀ p ∈ G,reference p ≤ (33/100 : ℝ)*V*w p) :
    (1/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ G,(T p-reference p) := by
  have howner := near_full_owner_lower P G hGP w T lo eta C V hlo heta hC hV hNear hW hAll hUpper hBudget
  have hw0 (p : α) (hp : p ∈ P) : 0 ≤ w p := hlo.trans (hW p hp).1
  have hsub : (∑ p ∈ G,w p) ≤ ∑ p ∈ P,w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hGP (fun p hp _ => hw0 p hp)
  have href : (∑ p ∈ G,reference p) ≤ (33/100 : ℝ)*V*(∑ p ∈ P,w p) := by
    calc
      _ ≤ ∑ p ∈ G,(33/100 : ℝ)*V*w p := Finset.sum_le_sum hReference
      _ = (33/100 : ℝ)*V*(∑ p ∈ G,w p) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub (by positivity)
  rw [Finset.sum_sub_distrib]
  linarith

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin
  ErdosPrimeInputs.MertensStrong ErdosInverseCounts
  NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable

theorem actual_owner_local_comparison_jb247_oai :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
      ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P : ℕ,P.Prime → P0 ≤ P →
      ∀ R theta eta : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) → (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
      0 ≤ eta → eta ≤ eta0 →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ t ∈ smallPrimeSet (P : ℝ),q.Coprime t) →
      (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet (P : ℝ) ∧
        (∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t) ∧
        ∀ t ∈ (p*q).primeFactors,P ≤ t) →
      (1-eta)*((primeBin R theta).card : ℝ) ≤
        (((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)).card : ℝ) →
      ∀ reference : ℕ → ℝ,
      (∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
        reference p ≤ (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
      (1/100 : ℝ)*primeProduct (P : ℝ)*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
        ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
          ((modulusCount Y (smallPrimeSet (P : ℝ)) a (p*q) : ℝ)-reference p) := by
  obtain ⟨C,eta0,hC,heta0,heta01,hBudget,P0,hP0,hUpper⟩ := primeHypothetical_uniform_upper
  refine ⟨eta0,heta0,heta01,P0,hP0,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hFull⟩ := hypothetical_full_bin_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨w0,hw0,hF⟩ := hFull rho xi hrho hxi
  refine ⟨w0,hw0,?_⟩
  intro w hw P hPrime hP R theta eta hPl hPu hR hThetaLo hThetaHi heta hetaU
    Y q hY hq r a hDen hNum hBand hqSmall hGeometry hNear reference hReference
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le hThetaLo
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hPrime.one_lt
  have hAll := hF w hw P R theta hPl hPu hR hThetaLo hThetaHi Y q hY hq r a hDen hNum
    hBand hqSmall (fun p hp =>
      ⟨(hGeometry p hp).1,(hGeometry p hp).2.1,(hGeometry p hp).2.2.1,(hGeometry p hp).2.2.2.1⟩)
  have hWeight := original_bin_weight_range Y q R theta (Nat.cast_nonneg Y)
    (show (0 : ℝ) < q by exact_mod_cast hq) hR0 ht.le hThetaHi
  have hPointUpper : ∀ p ∈ primeBin R theta,primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q p ≤
      C*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q)) := by
    intro p hp
    obtain ⟨hpPrime,hplo,hphi⟩ := (mem_primeBin hR0.le ht.le p).mp hp
    have hb := hBand p ⟨hplo.le,hphi⟩
    have hid := reference_rpow hP1 (show (0 : ℝ) < Y by exact_mod_cast hY)
      (hR0.trans hplo) (show (0 : ℝ) < q by exact_mod_cast hq)
    have hJ : (P : ℝ)^2 ≤ (Y : ℝ)/(p*q : ℕ) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hP1.le (show (2 : ℝ) ≤ lengthExponent P Y p q by linarith)
      rw [hid] at hh
      simpa only [Real.rpow_ofNat,referenceLength,Nat.cast_mul] using hh
    have hh := hUpper P hPrime hP Y q p r a hY hpPrime (hGeometry p hp).1
      (hGeometry p hp).2.2.2.2 hJ
    simpa only [Nat.cast_mul,mul_assoc,mul_left_comm,mul_comm] using hh
  have hBudget' : 2*C*eta ≤ (1/20 : ℝ) :=
    (mul_le_mul_of_nonneg_left hetaU (by positivity : 0 ≤ 2*C)).trans hBudget
  have hh := near_full_owner_comparison (primeBin R theta)
    ((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)) (Finset.filter_subset _ _)
    (fun p => (Y : ℝ)/((p : ℝ)*q)) (primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q)
    reference ((Y : ℝ)/(((1+theta)*R)*q)) eta C (primeProduct (P : ℝ))
    hWeight.1 heta hC.le (actual_primeProduct_pos _).le hNear hWeight.2 hAll hPointUpper hBudget' hReference
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,ha⟩ := Finset.mem_filter.mp hp
  rw [primeHypothetical_agrees Y _ a r q p ((mem_primeBin hR0.le ht.le p).mp hp).1 ha]

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247_oai := @OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247_oai
