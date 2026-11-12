-- Prove2me | solution 1 for OAI.Erdos970.ErdosVarianceMoments.finite_joint_moment_estimate_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:59.407408+00:00
-- url     : https://prove2.me/submissions/c1d4c039-092c-417c-b409-349f747bc506

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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositionDensities
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.decEq

theorem affine_forbidden_injective (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    Function.Injective (fun x : ZMod p => c-(u : ZMod p)*x) := by
  intro x y h
  have hm : (u : ZMod p)*x = (u : ZMod p)*y := by linear_combination -h
  have hh := congrArg (fun z : ZMod p => (↑(u⁻¹) : ZMod p)*z) hm
  simpa only [← mul_assoc,u.inv_mul,one_mul] using hh

theorem forbiddenClasses_card (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    (forbiddenClasses S p u c).card = (positionResidues S p).card := by
  have he : forbiddenClasses S p u c = (positionResidues S p).image (fun x => c-(u : ZMod p)*x) := by
    simp only [forbiddenClasses,positionResidues,Finset.image_image,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ (affine_forbidden_injective p u c)]

theorem mem_forbiddenClasses (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ forbiddenClasses S p u c ↔ ∃ j ∈ S,x+(u : ZMod p)*(j : ZMod p) = c := by
  simp only [forbiddenClasses,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩

theorem positionResidues_le_positions (S : Finset ℕ) (p : ℕ) : (positionResidues S p).card ≤ S.card :=
  Finset.card_image_le

theorem positionResidues_le_modulus (S : Finset ℕ) (p : ℕ) [NeZero p] : (positionResidues S p).card ≤ p := by
  have hh := Finset.card_le_univ (positionResidues S p)
  simpa only [ZMod.card] using hh

theorem forbiddenClasses_full_of_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) (hfull : (positionResidues S p).card = p) :
    forbiddenClasses S p u c = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp only [Finset.card_univ,ZMod.card,forbiddenClasses_card,hfull]
  exact le_rfl

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem positionDensity_bounds (S : Finset ℕ) (p : ℕ) [NeZero p] :
    0 ≤ positionDensity S p ∧ positionDensity S p ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨by dsimp [positionDensity] <;> positivity,?_⟩
  apply (div_le_one hp).mpr
  exact_mod_cast positionResidues_le_modulus S p

theorem positionDensity_le_two (S : Finset ℕ) (hS : S.card ≤ 2) (p : ℕ) [NeZero p] :
    positionDensity S p ≤ 2/(p : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (positionResidues_le_positions S p).trans hS

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_MobiusCoprimeExpansion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCoprimeResidueInterval
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable

theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem coprime_indicator (H : ℕ) (hH : 0 < H) (m : ℤ) :
    (∑ d ∈ H.divisors, if (d : ℤ) ∣ m then (μ d : ℝ) else 0) =
      if H.Coprime m.natAbs then 1 else 0 := by
  have hg : 0 < H.gcd m.natAbs := Nat.gcd_pos_of_pos_left m.natAbs hH
  have hf : H.divisors.filter (fun d : ℕ => (d : ℤ) ∣ m) = (H.gcd m.natAbs).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Int.natCast_dvd,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdH,_⟩,hdm⟩
      exact ⟨⟨hdH,hdm⟩,hg.ne'⟩
    · rintro ⟨⟨hdH,hdm⟩,_⟩
      exact ⟨⟨hdH,hH.ne'⟩,hdm⟩
  rw [← Finset.sum_filter,hf,moebius_divisor_sum]

theorem moebius_abs_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

theorem moebius_density (H : ℕ) (hH : 0 < H) :
    (∑ d ∈ H.divisors, (μ d : ℝ)/(d : ℝ)) = (H.totient : ℝ)/(H : ℝ) := by
  have ht : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, (d.totient : ℝ)) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp ht H hH
  rw [Nat.sum_divisorsAntidiagonal (fun d k => (μ d : ℝ)*(k : ℝ))] at hi
  apply (eq_div_iff (show (H : ℝ) ≠ 0 by exact_mod_cast hH.ne')).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ d ∈ H.divisors, (μ d : ℝ)*((H/d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
      ring
    _ = _ := hi

theorem coprime_count_expansion (H : ℕ) (hH : 0 < H) (C : Finset ℤ) (F : ℤ → Prop) :
    ((C.filter (fun m => H.Coprime m.natAbs ∧ F m)).card : ℝ) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*((C.filter (fun m => (d : ℤ) ∣ m ∧ F m)).card : ℝ) := by
  classical
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hF : F m
  · simpa only [hF,and_true,mul_ite,mul_one,mul_zero] using (coprime_indicator H hH m).symm
  · simp [hF]

end ErdosCoprimeResidueInterval

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



namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem crt_coordinate_val {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (r : ZMod (∏ i,m i)) (i : ι) :
    (ZMod.prodEquivPi m hcop r) i = (r.val : ZMod (m i)) := by
  calc
    (ZMod.prodEquivPi m hcop r) i =
        (ZMod.prodEquivPi m hcop (r.val : ZMod (∏ j,m j))) i := by
      rw [ZMod.natCast_zmod_val]
    _ = (r.val : ZMod (m i)) := by
      rw [ZMod.prodEquivPi_apply]
      exact map_natCast (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) r.val

theorem literal_residue_choices_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (E : ∀ i,Finset (ZMod (m i))) :
    (Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i)).card =
      ∏ i,(E i).card := by
  have he : Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i) =
      ErdosInverseCRT.crtResidues m hcop E := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ErdosInverseCRT.mem_crtResidues,
      crt_coordinate_val]
  rw [he,ErdosInverseCRT.crtResidues_card]

theorem canonical_filter_card (N : ℕ) [NeZero N] (f : ℕ → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun r : ZMod N => f r.val)).card =
      ((Finset.range N).filter f).card := by
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr r.val_lt,(Finset.mem_filter.mp hr).2⟩
  · intro r _hr s _hs he
    exact ZMod.val_injective N he
  · intro n hn
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    refine ⟨(n : ZMod N),?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
      exact (Finset.mem_filter.mp hn).2
    · simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hlt]

theorem mem_allowedClasses (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ allowedClasses S p u c ↔ ∀ j ∈ S,x+(u : ZMod p)*(j : ZMod p) ≠ c := by
  simp only [allowedClasses,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_forbiddenClasses,
    not_exists,not_and]

theorem allowedClasses_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) :
    (allowedClasses S p u c).card = p-(positionResidues S p).card := by
  rw [allowedClasses,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card,
    forbiddenClasses_card]

end ErdosVarianceMoments



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

end Erdos66Dependency.ResidueLifts



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

theorem binary_modulus_product (d l : ℕ) : (∏ i : Bool,binaryModuli d l i) = d*l := by
  simp [binaryModuli,mul_comm]

theorem divisibleResidues_card (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) : (divisibleResidues d l h A).card = A.card := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  unfold divisibleResidues
  rw [ErdosInverseCRT.integerCRTResidues_card _ _ _ hN]
  simp only [Fintype.prod_bool,binaryClasses,Finset.card_singleton,mul_one]

theorem divisibleResidues_range (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) :
    divisibleResidues d l h A ⊆ Finset.Ico 0 (d*l : ℕ) := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  simpa only [divisibleResidues,binary_modulus_product] using ErdosInverseCRT.integerCRTResidues_subset
    (binaryModuli d l) (binary_coprime d l h) (binaryClasses d l A) hN

theorem mem_divisibleResidues (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) (m : ℤ) :
    m % (d*l : ℕ) ∈ divisibleResidues d l h A ↔ (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  unfold divisibleResidues
  rw [← binary_modulus_product d l,ErdosInverseCRT.emod_mem_integerCRTResidues _ _ _ hN]
  simp only [Bool.forall_bool,binaryClasses,binaryModuli]
  change ((m : ZMod d) ∈ ({0} : Finset (ZMod d)) ∧ (m : ZMod l) ∈ A) ↔ _
  rw [Finset.mem_singleton,ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem divisible_residue_count (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) (b c : ℤ) :
    |(((Finset.Ico b c).filter (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A)).card : ℝ) -
      ((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l)| ≤ A.card := by
  have he : (Finset.Ico b c).filter (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A) =
      Erdos66Dependency.ResidueLifts.liftsOn (Finset.Ico b c) (d*l : ℕ) (divisibleResidues d l h A) := by
    ext m
    simp only [Erdos66Dependency.ResidueLifts.liftsOn,Finset.mem_filter,
      mem_divisibleResidues d l hd hl h A]
  rw [he]
  have hh := Erdos66Dependency.ResidueLifts.count_error b c (d*l : ℕ) (divisibleResidues d l h A)
    (by exact_mod_cast Nat.mul_pos hd hl) (divisibleResidues_range d l hd hl h A)
  simpa only [divisibleResidues_card d l hd hl h A,Nat.cast_mul,Int.cast_mul,Int.cast_natCast] using hh

end ErdosCoprimeResidueInterval



namespace ErdosCoprimeResidueInterval
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable

theorem coprime_residue_count (H l : ℕ) (hH : 0 < H) (hl : 0 < l)
    (hcop : H.Coprime l) (A : Finset (ZMod l)) (b c : ℤ) :
    |((coprimeResidues H l A b c).card : ℝ) - ((Finset.Ico b c).card : ℝ)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤
        (H.divisors.card : ℝ)*(A.card : ℝ) := by
  classical
  let f (d : ℕ) := (((Finset.Ico b c).filter
    (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A)).card : ℝ)
  have hcount : ((coprimeResidues H l A b c).card : ℝ) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*f d := by
    convert coprime_count_expansion H hH (Finset.Ico b c) (fun m : ℤ => (m : ZMod l) ∈ A) using 1
    · apply congrArg (fun S : Finset ℤ => (S.card : ℝ))
      ext m
      simp only [coprimeResidues,Finset.mem_filter]
    · apply Finset.sum_congr rfl
      intro d _
      congr 1
      apply congrArg (fun S : Finset ℤ => (S.card : ℝ))
      ext m
      simp only [Finset.mem_filter]
  have he : ((coprimeResidues H l A b c).card : ℝ) - ((Finset.Ico b c).card : ℝ)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l)) := by
    rw [hcount]
    rw [← moebius_density H hH]
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    dsimp only [f]
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ H.divisors, |(μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ H.divisors, (A.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdl : d.Coprime l := Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors hd) hcop
      have herr := divisible_residue_count d l hd0 hl hdl A b c
      change |(μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l))| ≤ (A.card : ℝ)
      rw [abs_mul]
      exact (mul_le_mul (moebius_abs_le_one d) herr (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

end ErdosCoprimeResidueInterval



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

theorem mem_realCoprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℝ) (m : ℤ) :
    m ∈ realCoprimeResidues H l A b c ↔
      b ≤ (m : ℝ) ∧ (m : ℝ) < c ∧ H.Coprime m.natAbs ∧ (m : ZMod l) ∈ A := by
  simp only [realCoprimeResidues,coprimeResidues,Finset.mem_filter,Finset.mem_Ico,
    Int.ceil_le,Int.lt_ceil,and_assoc]

theorem ceiling_interval_error (b c : ℝ) (hbc : b ≤ c) :
    |((Finset.Ico ⌈b⌉ ⌈c⌉).card : ℝ)-(c-b)| ≤ 1 := by
  rw [Erdos66Dependency.ResidueLifts.card_Ico_real (Int.ceil_mono hbc),abs_le]
  constructor <;> linarith [Int.le_ceil b,Int.ceil_lt_add_one b,Int.le_ceil c,Int.ceil_lt_add_one c]

theorem coprime_density_bounds (H l : ℕ) (hH : 0 < H) (hl : 0 < l) (A : Finset (ZMod l)) :
    0 ≤ ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) ∧
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) ≤ (A.card : ℝ) := by
  have hV : (H.totient : ℝ)/(H : ℝ) ≤ 1 :=
    (div_le_one (show (0 : ℝ) < H by exact_mod_cast hH)).mpr (by exact_mod_cast Nat.totient_le H)
  have hAl : (A.card : ℝ)/(l : ℝ) ≤ A.card :=
    div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hl)
  refine ⟨by positivity,?_⟩
  exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans (by simpa only [one_mul] using hAl)

theorem real_coprime_residue_count (H l : ℕ) (hH : 0 < H) (hl : 0 < l)
    (hcop : H.Coprime l) (A : Finset (ZMod l)) (b c : ℝ) (hbc : b ≤ c) :
    |((realCoprimeResidues H l A b c).card : ℝ) - (c-b)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤
        2*(H.divisors.card : ℝ)*(A.card : ℝ) := by
  let rho := ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))
  let L := ((Finset.Ico ⌈b⌉ ⌈c⌉).card : ℝ)
  have hr := coprime_density_bounds H l hH hl A
  have hbase := coprime_residue_count H l hH hl hcop A ⌈b⌉ ⌈c⌉
  have hround := ceiling_interval_error b c hbc
  have hpert : |(L-(c-b))*rho| ≤ A.card := by
    rw [abs_mul,abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hround hr.1).trans (by simpa only [one_mul] using hr.2)
  have ht : (1 : ℝ) ≤ H.divisors.card := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hH.ne'⟩)
  have htA := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg A.card)
  have he : ((realCoprimeResidues H l A b c).card : ℝ)-(c-b)*rho =
      (((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*rho)+(L-(c-b))*rho := by
    dsimp [realCoprimeResidues]
    ring
  change |((realCoprimeResidues H l A b c).card : ℝ)-(c-b)*((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤ _
  rw [mul_assoc,he]
  have hh := abs_add_le (((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*rho) ((L-(c-b))*rho)
  change |((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤ _ at hbase
  rw [mul_assoc] at hbase
  nlinarith [hh,hpert,hbase,htA]

end ErdosCoprimeResidueInterval


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

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem prime_residue_choices_card (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (E : ∀ p : ℕ,Finset (ZMod p)) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)).card =
      ∏ p ∈ P,(E p).card := by
  have hcop : Pairwise (fun i j : P => Nat.Coprime i.val j.val) := by
    intro i j hij
    exact (Nat.coprime_primes (hP i i.property) (hP j j.property)).mpr
      (fun he => hij (Subtype.ext he))
  have he : (∏ i : P,(i : ℕ)) = ∏ p ∈ P,p := Finset.prod_coe_sort P (fun p => p)
  let : NeZero (∏ i : P,(i : ℕ)) := ⟨by rw [he];exact NeZero.ne _⟩
  have hc := literal_residue_choices_card (fun i : P => (i : ℕ)) hcop (fun i => E i)
  have hn := (canonical_filter_card (∏ i : P,(i : ℕ))
    (fun n => ∀ i : P,(n : ZMod i.val) ∈ E i.val)).symm.trans hc
  calc
    _ = ((Finset.range (∏ p ∈ P,p)).filter (fun n => ∀ p ∈ P,(n : ZMod p) ∈ E p)).card :=
      canonical_filter_card _ _
    _ = _ := by
      simpa only [he,Finset.prod_coe_sort P (fun p => (E p).card),Subtype.forall] using hn

theorem prime_unit_avoidance_card (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (u : ∀ p : ℕ,(ZMod p)ˣ) (c : ∀ p : ℕ,ZMod p) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p)).card =
      ∏ p ∈ P,(p-(positionResidues S p).card) := by
  let E (p : ℕ) : Finset (ZMod p) :=
    if hp : p = 0 then ∅ else @allowedClasses S p ⟨hp⟩ (u p) (c p)
  have hmem (p : ℕ) (hp : p ∈ P) (x : ZMod p) :
      x ∈ E p ↔ ∀ j ∈ S,x+(u p : ZMod p)*(j : ZMod p) ≠ c p := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,mem_allowedClasses]
  have hcard (p : ℕ) (hp : p ∈ P) : (E p).card = p-(positionResidues S p).card := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,allowedClasses_card]
  have hf : Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p) =
      Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p) := by
    apply Finset.filter_congr
    intro r _hr
    exact forall_congr' (fun p => forall_congr' (fun hp => (hmem p hp _).symm))
  rw [hf,prime_residue_choices_card P hP E]
  exact Finset.prod_congr rfl hcard

theorem product_allowed_eq_density (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    ((∏ p ∈ P,(p-(positionResidues S p).card) : ℕ) : ℝ) =
      ((∏ p ∈ P,p : ℕ) : ℝ)*jointDensity P S := by
  rw [Nat.cast_prod,Nat.cast_prod,jointDensity,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  have hle := positionResidues_le_modulus S p
  rw [Nat.cast_sub hle,positionDensity]
  have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem primeResidueSet_card (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) :
    (primeResidueSet P hP E).card = ∏ p ∈ P,(E p).card := by
  let : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  exact prime_residue_choices_card P hP E

theorem cast_int_residue (M t : ℕ) [NeZero M] (htM : t ∣ M) (n : ℤ) :
    (((n : ZMod M).val : ℕ) : ZMod t) = (n : ZMod t) := by
  have hh := congrArg (ZMod.castHom htM (ZMod t)) (ZMod.natCast_zmod_val (n : ZMod M))
  simpa only [map_natCast,map_intCast] using hh

theorem int_mem_primeResidueSet (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) (n : ℤ) :
    (n : ZMod (∏ p ∈ P,p)) ∈ primeResidueSet P hP E ↔ ∀ p ∈ P,(n : ZMod p) ∈ E p := by
  let : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  change ((n : ZMod (∏ p ∈ P,p)) ∈ Finset.univ.filter (fun r => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact forall_congr' (fun p => forall_congr' (fun hp => by
    rw [cast_int_residue _ p (Finset.dvd_prod_of_mem _ hp) n]))

theorem integerPrimeIntersection_error (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c) :
    |((integerPrimeIntersection H P E b c).card : ℝ)-
      (c-b)*((H.totient : ℝ)/(H : ℝ))*(∏ p ∈ P,((E p).card : ℝ)/(p : ℝ))| ≤
      2*(H.divisors.card : ℝ)*(∏ p ∈ P,((E p).card : ℝ)) := by
  have hL : 0 < ∏ p ∈ P,p := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hcop : H.Coprime (∏ p ∈ P,p) := Nat.coprime_prod_right_iff.mpr hHP
  have he : integerPrimeIntersection H P E b c =
      ErdosCoprimeResidueInterval.realCoprimeResidues H (∏ p ∈ P,p) (primeResidueSet P hP E) b c := by
    ext n
    simp only [integerPrimeIntersection,Finset.mem_filter,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil,
      ErdosCoprimeResidueInterval.mem_realCoprimeResidues,int_mem_primeResidueSet,and_assoc]
  rw [he]
  have hh := ErdosCoprimeResidueInterval.real_coprime_residue_count H _ hH hL hcop
    (primeResidueSet P hP E) b c hbc
  simpa only [primeResidueSet_card,Nat.cast_prod,Finset.prod_div_distrib] using hh

end ErdosVarianceMoments

end

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

namespace ErdosVarianceMoments
open NumberTheoryLean
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem actual_intersection_mass (H : ℕ) (P : Finset ℕ)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) :
    BonferroniBlocks.intersectionMass (unitIntervalIntegers H b c) (fun _ => 1)
      (fun p n => (n : ZMod p) ∈ E p) P = (integerPrimeIntersection H P E b c).card := by
  have he : integerPrimeIntersection H P E b c =
      (unitIntervalIntegers H b c).filter (fun n => ∀ p ∈ P,(n : ZMod p) ∈ E p) := by
    ext n
    simp only [integerPrimeIntersection,unitIntervalIntegers,Finset.mem_filter,and_assoc]
  rw [he,Finset.card_filter,Nat.cast_sum]
  simp only [BonferroniBlocks.intersectionMass,BonferroniBlocks.intersectionValue,one_mul,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs <;> rfl

theorem integerRemainder_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c)
    (d : ℕ) (hd : d ∣ ∏ p ∈ P,p) :
    |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
      (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d| ≤
      2*(H.divisors.card : ℝ)*(d : ℝ) := by
  have hsq : Squarefree (∏ p ∈ P,p) := IntervalBoundingSieve.squarefree_primeSet_product P hP
  have hdsq := hsq.squarefree_of_dvd hd
  have hsub : d.primeFactors ⊆ P := by
    rw [← Nat.primeFactors_prod hP]
    exact Nat.primeFactors_mono hd hsq.ne_zero
  have hprime (p : ℕ) (hp : p ∈ d.primeFactors) : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have herr := integerPrimeIntersection_error H hH d.primeFactors hprime
    (fun p hp => hHP p (hsub hp)) E b c hbc
  have hcard : (∏ p ∈ d.primeFactors,((E p).card : ℝ)) ≤ d := by
    calc
      _ ≤ ∏ p ∈ d.primeFactors,(p : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro p hp
        let : NeZero p := ⟨(hprime p hp).ne_zero⟩
        have hh := Finset.card_le_univ (E p)
        rw [ZMod.card] at hh
        exact_mod_cast hh
      _ = d := by rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hdsq]
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
  rw [actual_intersection_mass]
  exact herr.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

theorem remainder_sum_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c)
    (v s : ℝ) (hD : 1 ≤ v^s) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
      |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
        (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d|) ≤
      4*(H.divisors.card : ℝ)*(v^s)^2 := by
  let D := v^s
  let F := RealFundamentalSieve.levelDivisors P v s
  have hsize (d : ℕ) (hd : d ∈ F) : (d : ℝ) ≤ D := (Finset.mem_filter.mp hd).2
  have hsub : F ⊆ Finset.range (⌊D⌋₊+1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by dsimp [D] <;> linarith)).mpr (hsize d hd)))
  have hcard : (F.card : ℝ) ≤ 2*D := by
    have hc : (F.card : ℝ) ≤ ((⌊D⌋₊+1 : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ D by dsimp [D] <;> linarith)
    push_cast at hc
    dsimp [D] at *
    linarith
  have hsum : (∑ d ∈ F,
      |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
        (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d|) ≤
      (F.card : ℝ)*(2*(H.divisors.card : ℝ)*D) := by
    calc
      _ ≤ ∑ _d ∈ F,2*(H.divisors.card : ℝ)*D := by
        apply Finset.sum_le_sum
        intro d hd
        exact (integerRemainder_bound H hH P hP hHP E b c hbc d
          (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).trans
            (mul_le_mul_of_nonneg_left (hsize d hd) (by positivity))
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  have hnon : 0 ≤ 2*(H.divisors.card : ℝ)*D := by dsimp [D] <;> positivity
  have hh := mul_le_mul_of_nonneg_right hcard hnon
  exact hsum.trans (by dsimp [D] at hh ⊢ <;> nlinarith)

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SmallModelMeasure
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem atomWeight_pos (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    0 < atomWeight R xi w H C0 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hphi : (0 : ℝ) < H.totient := by exact_mod_cast Nat.totient_pos.mpr hH
  have hT0 : (0 : ℝ) < divisorModulus w H := by exact_mod_cast divisorModulus_pos w H
  have hT1 : (0 : ℝ) < (coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr (coprimeModulus_pos w H)
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    dsimp [modelLength,interceptScale]
    positivity
  unfold atomWeight
  positivity

theorem modelMass_card (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (E : ModelPoint w H → Prop) :
    modelMass R xi w H C0 E =
      (((modelUniverse R xi w H C0).filter E).card : ℝ)*atomWeight R xi w H C0 := by
  simp only [modelMass,Finset.sum_const,nsmul_eq_mul]

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel

theorem divisorPhaseUnit_coe (H : ℕ) (C0 m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hm : m.natAbs.Coprime H) (t : ℕ) (htH : t ∣ H) :
    (divisorPhaseUnit H C0 m hC0 hm t htH : ZMod t) = divisorPhase C0 m t := rfl

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualModelTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

theorem jointCondition_split (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) :
    jointCondition w H C0 qA beta delta S v ↔
      (∀ t ∈ divisorPrimes w H,∀ j ∈ S,patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ beta t) ∧
      (∀ t ∈ coprimePrimes w H,∀ j ∈ S,patternPValue w H v.2 t*(qA : ZMod t)*
        ((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t) := by
  constructor
  · intro h
    exact ⟨fun t ht j hj => (h j hj).1 t ht,fun t ht j hj => (h j hj).2 t ht⟩
  · rintro ⟨h0,h1⟩ j hj
    exact ⟨fun t ht => h0 t ht j hj,fun t ht => h1 t ht j hj⟩

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CoprimePositionSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointCondition_coordinates (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ) (s : Pattern w H) :
    jointCondition w H C0 qA beta delta S (m,s) ↔
      divisorJoint w H C0 beta S m s.2 ∧ coprimeJoint w H qA delta S m s.1 :=
  jointCondition_split w H C0 qA beta delta S (m,s)

theorem divisorJoint_card (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (divisorJoint w H C0 beta S m)).card =
      ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ :=
    if ht : t ∣ H then divisorPhaseUnit H C0 m hC0 hm t ht else 1
  have hunit (t : ℕ) (ht : t ∈ divisorPrimes w H) : (u t : ZMod t) = divisorPhase C0 m t := by
    simp only [u,dite_eq_left (Finset.mem_filter.mp ht).2,divisorPhaseUnit_coe]
  have hP (t : ℕ) (ht : t ∈ divisorPrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ divisorPrimes w H,t) := ⟨(divisorModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (divisorPrimes w H) S hP u beta
  have he : Finset.univ.filter (divisorJoint w H C0 beta S m) =
      Finset.univ.filter (fun k : ZMod (divisorModulus w H) =>
        ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ beta t) := by
    apply Finset.filter_congr
    intro k _hk
    unfold divisorJoint
    exact forall_congr' (fun t => forall_congr' (fun ht => by rw [hunit t ht]))
  rw [he]
  exact hh

theorem conditional_pattern_card (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).card*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have he : Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s)) =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).product
        (Finset.univ.filter (divisorJoint w H C0 beta S m)) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.product_eq_sprod,Finset.mem_product,
      jointCondition_coordinates,and_comm]
  rw [he,Finset.product_eq_sprod,Finset.card_product,divisorJoint_card w H C0 beta S m hC0 hm]

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem patternPrimeUnit_coe (w : ℝ) (H : ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    (patternPrimeUnit w H p t ht : ZMod t) = (p.val.val : ZMod t) := by
  change ZMod.castHom ht (ZMod t) p.val = _
  calc
    ZMod.castHom ht (ZMod t) p.val =
      ZMod.castHom ht (ZMod t) (p.val.val : ZMod (coprimeModulus w H)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast (ZMod.castHom ht (ZMod t)) p.val.val

theorem unit_mul_eq_iff {M : Type*} [Monoid M] (u : Mˣ) (x c : M) :
    (u : M)*x = c ↔ x = (u⁻¹ : Mˣ)*c := by
  constructor
  · intro h
    have hh := congrArg (fun y : M => (u⁻¹ : Mˣ)*y) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

theorem mem_coprimeForbidden (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) (x : ZMod t) :
    x ∈ coprimeForbidden w H qA delta S p t ht hqA ↔
      ∃ j ∈ S,(p.val.val : ZMod t)*(qA : ZMod t)*(x+(H : ZMod t)*(j : ZMod t)) = delta t := by
  rw [coprimeForbidden,mem_forbiddenClasses]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _hj
  have hh := unit_mul_eq_iff (coprimeCoefficientUnit w H qA p t ht hqA)
    (x+(H : ZMod t)*(j : ZMod t)) (delta t)
  have hc : (coprimeCoefficientUnit w H qA p t ht hqA : ZMod t) =
      (p.val.val : ZMod t)*(qA : ZMod t) := by
    simpa only [coprimeCoefficientUnit,Units.val_mul,ZMod.coe_unitOfCoprime] using
      congrArg (fun v : ZMod t => v*(qA : ZMod t))
        (patternPrimeUnit_coe w H p t (Finset.dvd_prod_of_mem _ ht))
  rw [hc] at hh
  simpa only [coprimeShiftUnit,ZMod.coe_unitOfCoprime] using hh.symm

theorem coprimeForbidden_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) :
    (coprimeForbidden w H qA delta S p t ht hqA).card = (positionResidues S t).card :=
  forbiddenClasses_card _ _ _ _

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem coprimeForbiddenFamily_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (t : ℕ) (ht : t ∈ coprimePrimes w H) :
    (coprimeForbiddenFamily w H qA delta S p hqA t).card = (positionResidues S t).card := by
  simp only [coprimeForbiddenFamily,dite_eq_left ht,coprimeForbidden_card]

theorem coprimeJoint_avoidance (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (m : ℤ) :
    coprimeJoint w H qA delta S m p ↔
      ∀ t ∈ coprimePrimes w H,(m : ZMod t) ∉ coprimeForbiddenFamily w H qA delta S p hqA t := by
  unfold coprimeJoint
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  simp only [coprimeForbiddenFamily,dite_eq_left ht,mem_coprimeForbidden,not_exists,not_and]

theorem nonzero_positionDensity_two (P S : Finset ℕ) (hS : S.card ≤ 2)
    (hne : jointDensity P S ≠ 0) (h2 : 2 ∈ P) : positionDensity S 2 ≤ 1/2 := by
  have hn : 1-positionDensity S 2 ≠ 0 := (Finset.prod_ne_zero_iff.mp hne) 2 h2
  have hcard := positionResidues_le_positions S 2
  have hnot : (positionResidues S 2).card ≠ 2 := by
    intro he
    apply hn
    norm_num [positionDensity,he]
  have hle : (positionResidues S 2).card ≤ 1 := by omega
  unfold positionDensity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num)

theorem coprimePositionSurvivors_sieve_sum (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (b c : ℝ) :
    ((coprimePositionSurvivors w H qA delta S p b c).card : ℝ) =
      ∑ m ∈ unitIntervalIntegers H b c,(1 : ℝ)*BonferroniBlocks.survives (coprimePrimes w H)
        (fun t => (m : ZMod t) ∈ coprimeForbiddenFamily w H qA delta S p hqA t) := by
  rw [coprimePositionSurvivors,Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,one_mul,BonferroniBlocks.survives,
    coprimeJoint_avoidance w H qA delta S p hqA]
  apply Finset.sum_congr rfl
  intro m _hm
  split_ifs <;> rfl

theorem coprimePositionSurvivors_estimate (w : ℝ) (hw : 2 ≤ w) (s : ℝ) (hs : 480024 ≤ s)
    (H qA : ℕ) (hH : 0 < H) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hS : S.card ≤ 2)
    (p : (ZMod (coprimeModulus w H))ˣ) (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (b c : ℝ) (hbc : b ≤ c) (hne : jointDensity (coprimePrimes w H) S ≠ 0) :
    |((coprimePositionSurvivors w H qA delta S p b c).card : ℝ)-
      ((c-b)*((H.totient : ℝ)/(H : ℝ)))*jointDensity (coprimePrimes w H) S| ≤
      ((c-b)*((H.totient : ℝ)/(H : ℝ)))*jointDensity (coprimePrimes w H) S*Real.exp (-s/96)+
        4*(H.divisors.card : ℝ)*(w^s)^2 := by
  let P := coprimePrimes w H
  let E := coprimeForbiddenFamily w H qA delta S p hqA
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have hsize (t : ℕ) (ht : t ∈ P) : (t : ℝ) ≤ w :=
    (Nat.le_floor_iff (by linarith)).mp (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).2
  have hHP (t : ℕ) (ht : t ∈ P) : H.Coprime t :=
    ((hP t ht).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp ht).2).symm
  have hge (t : ℕ) (ht : t ∈ P) : residueDensity E t = positionDensity S t := by
    unfold residueDensity positionDensity
    rw [coprimeForbiddenFamily_card w H qA delta S p hqA t ht]
  have hg0 (t : ℕ) (ht : t ∈ P) : 0 ≤ residueDensity E t := by
    rw [hge t ht]
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact (positionDensity_bounds S t).1
  have hdim (t : ℕ) (ht : t ∈ P) : residueDensity E t ≤ 2/(t : ℝ) := by
    rw [hge t ht]
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact positionDensity_le_two S hS t
  have htwo (h2 : 2 ∈ P) : residueDensity E 2 ≤ 1/2 := by
    rw [hge 2 h2]
    exact nonzero_positionDensity_two P S hS hne h2
  have hX : 0 ≤ (c-b)*((H.totient : ℝ)/(H : ℝ)) := mul_nonneg (sub_nonneg.mpr hbc) (by positivity)
  have hprod : (∏ t ∈ P,(1-residueDensity E t)) = jointDensity P S :=
    Finset.prod_congr rfl (fun t ht => by rw [hge t ht])
  have hf := RealFundamentalSieve.fundamental_lemma (unitIntervalIntegers H b c) (fun _ => 1)
    (fun _ _ => by norm_num) (fun t m => (m : ZMod t) ∈ E t)
    w s P ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E)
    hw hs hX hP hsize hg0 hdim htwo
  rw [hprod] at hf
  rw [coprimePositionSurvivors_sieve_sum w H qA delta S p hqA b c]
  have hD : 1 ≤ w^s := Real.one_le_rpow (by linarith) (by linarith)
  have hr := remainder_sum_bound H hH P hP hHP E b c hbc w s hD
  exact hf.trans (add_le_add le_rfl hr)

end ErdosVarianceMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_JointModelCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem zero_jointDensity_full_class (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hz : jointDensity P S = 0) : ∃ t ∈ P,(positionResidues S t).card = t := by
  obtain ⟨t,ht,hzero⟩ := Finset.prod_eq_zero_iff.mp hz
  have htpos : (0 : ℝ) < t := by exact_mod_cast (hP t ht).pos
  have he : ((positionResidues S t).card : ℝ)/(t : ℝ) = 1 := by
    change 1-((positionResidues S t).card : ℝ)/(t : ℝ) = 0 at hzero
    linarith
  refine ⟨t,ht,?_⟩
  exact_mod_cast (div_eq_one_iff_eq htpos.ne').mp he

theorem zero_coprimeJoint (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (m : ℤ) :
    ¬coprimeJoint w H qA delta S m p := by
  obtain ⟨t,ht,hfull⟩ := zero_jointDensity_full_class (coprimePrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1) hz
  let : NeZero t := ⟨(LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.ne_zero⟩
  have he : coprimeForbidden w H qA delta S p t ht (hqA t ht) = Finset.univ :=
    forbiddenClasses_full_of_card _ _ _ _ hfull
  intro h
  have hav := (coprimeJoint_avoidance w H qA delta S p hqA m).mp h t ht
  apply hav
  simp only [coprimeForbiddenFamily,dite_eq_left ht,he,Finset.mem_univ]

theorem zero_coprimePositionSurvivors (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (hz : jointDensity (coprimePrimes w H) S = 0) (b c : ℝ) :
    coprimePositionSurvivors w H qA delta S p b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact zero_coprimeJoint w H qA delta S p hqA hz m (Finset.mem_filter.mp hm).2

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem unitInterval_eq_modelUnitIntegers (R xi : ℝ) (H : ℕ) (C0 : ℤ) :
    unitIntervalIntegers H (modelLeft R xi (C0 : ℝ)) (modelRight R xi (H : ℝ) (C0 : ℝ)) =
      modelUnitIntegers R xi H C0 := by
  ext m
  simp only [unitIntervalIntegers,modelUnitIntegers,modelIntegers,Finset.mem_filter,Nat.coprime_comm]

theorem joint_model_card (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      (∑ p : (ZMod (coprimeModulus w H))ˣ,
        (coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
          (modelRight R xi (H : ℝ) (C0 : ℝ))).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have hsplit : ((modelUniverse R xi w H C0).filter (jointCondition w H C0 qA beta delta S)).card =
      ∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card := by
    simp only [modelUniverse,Finset.product_eq_sprod,Finset.card_filter,Finset.sum_product]
  rw [hsplit]
  have hc : (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card) =
      (∑ m ∈ modelUnitIntegers R xi H C0,
        (Finset.univ.filter (coprimeJoint w H qA delta S m)).card)*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    exact conditional_pattern_card w H C0 qA beta delta S m hC0 (Finset.mem_filter.mp hm).2
  rw [hc]
  congr 1
  simp only [coprimePositionSurvivors,unitInterval_eq_modelUnitIntegers,Finset.card_filter]
  exact Finset.sum_comm

theorem joint_model_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) =
      atomWeight R xi w H C0*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S)*
        ∑ p : (ZMod (coprimeModulus w H))ˣ,
          ((coprimePositionSurvivors w H qA delta S p (modelLeft R xi (C0 : ℝ))
            (modelRight R xi (H : ℝ) (C0 : ℝ))).card : ℝ) := by
  rw [modelMass_card,joint_model_card R xi w H qA C0 beta delta S hC0,Nat.cast_mul,Nat.cast_sum,
    product_allowed_eq_density (divisorPrimes w H) S (fun t ht =>
      (NumberTheoryLean.LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)]
  change (_*((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S))*_ = _
  ring

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_JointModelDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_nonneg (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime) :
    0 ≤ jointDensity P S := by
  apply Finset.prod_nonneg
  intro t ht
  let : NeZero t := ⟨(hP t ht).ne_zero⟩
  exact sub_nonneg.mpr (positionDensity_bounds S t).2

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem jointDensity_le_one (P S : Finset ℕ) (hP : ∀ t ∈ P,t.Prime) : jointDensity P S ≤ 1 := by
  apply Finset.prod_le_one
  · intro t ht
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact sub_nonneg.mpr (positionDensity_bounds S t).2
  · intro t ht
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    have hh := (positionDensity_bounds S t).1
    linarith

theorem jointDensity_split (w : ℝ) (H : ℕ) (S : Finset ℕ) :
    jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  unfold jointDensity divisorPrimes coprimePrimes
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

theorem model_normalization_identity (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    atomWeight R xi w H C0*(divisorModulus w H : ℝ)*
      ((coprimeModulus w H).totient : ℝ)*
      (modelLength R xi (H : ℝ) (C0 : ℝ)*((H.totient : ℝ)/(H : ℝ))) = 1 := by
  have hHN : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hphi : (H.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hH).ne'
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    have hHR : (0 : ℝ) < H := by exact_mod_cast hH
    dsimp [modelLength,interceptScale]
    positivity
  unfold atomWeight
  field_simp

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MomentIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem finite_joint_moment_estimate_jb247_oai (R xi w : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) (hw : 2 ≤ w)
    (s : ℝ) (hs : 480024 ≤ s) (H qA : ℕ) (hH : 0 < H) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (S : Finset ℕ) (hS : S.card ≤ 2) :
    |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S*Real.exp (-s/96)+
        4*(H.divisors.card : ℝ)*(H : ℝ)/
          (modelLength R xi (H : ℝ) (C0 : ℝ)*(H.totient : ℝ))*(w^s)^2 := by
  let b := modelLeft R xi (C0 : ℝ)
  let c := modelRight R xi (H : ℝ) (C0 : ℝ)
  let Y := modelLength R xi (H : ℝ) (C0 : ℝ)
  let X := Y*((H.totient : ℝ)/(H : ℝ))
  let K0 := jointDensity (divisorPrimes w H) S
  let K1 := jointDensity (coprimePrimes w H) S
  let a0 := atomWeight R xi w H C0*(divisorModulus w H : ℝ)
  let N : ℝ := (coprimeModulus w H).totient
  let err := 4*(H.divisors.card : ℝ)*(w^s)^2
  let B := X*K1*Real.exp (-s/96)+err
  let f (p : (ZMod (coprimeModulus w H))ˣ) : ℝ :=
    (coprimePositionSurvivors w H qA delta S p b c).card
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hY : 0 < Y := by dsimp [Y,modelLength,interceptScale] <;> positivity
  have hX : 0 < X := mul_pos hY (div_pos (by exact_mod_cast Nat.totient_pos.mpr hH) hHR)
  have hbc : c-b = Y := by dsimp [c,b,modelRight,Y] <;> ring
  have hK0 := jointDensity_nonneg (divisorPrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have hK01 := jointDensity_le_one (divisorPrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have ha0 : 0 < a0 := mul_pos (atomWeight_pos R xi w H C0 hR hxi hH)
    (by exact_mod_cast divisorModulus_pos w H)
  have hnorm : a0*N*X = 1 := model_normalization_identity R xi w H C0 hR hxi hH
  have hpoint (p : (ZMod (coprimeModulus w H))ˣ) : |f p-X*K1| ≤ B := by
    by_cases hz : K1 = 0
    · have he := zero_coprimePositionSurvivors w H qA delta S p hqA hz b c
      simp only [f,he,Finset.card_empty,Nat.cast_zero,hz,mul_zero,sub_zero,abs_zero,B,zero_mul,zero_add]
      dsimp [err]
      positivity
    · have hh := coprimePositionSurvivors_estimate w hw s hs H qA hH delta S hS p hqA b c
        (by linarith) hz
      rw [hbc] at hh
      exact hh
  have hsum : |(∑ p,f p)-N*(X*K1)| ≤ N*B := by
    have hconst : (∑ _p : (ZMod (coprimeModulus w H))ˣ,X*K1) = N*(X*K1) := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul,N]
    rw [← hconst,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p,|f p-X*K1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : (ZMod (coprimeModulus w H))ˣ,B := Finset.sum_le_sum (fun p _ => hpoint p)
      _ = N*B := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul,N]
  have hmass : modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) = a0*K0*(∑ p,f p) := by
    rw [joint_model_mass R xi w H qA C0 beta delta S hC0]
    dsimp [a0,K0,f,b,c]
    ring
  have hbase : a0*K0*(N*(X*K1)) = K0*K1 := by
    calc
      _ = (a0*N*X)*(K0*K1) := by ring
      _ = _ := by rw [hnorm,one_mul]
  have htotal := jointDensity_split w H S
  change K0*K1 = _ at htotal
  rw [← htotal,hmass,← hbase,← mul_sub,abs_mul,abs_of_nonneg (mul_nonneg ha0.le hK0)]
  have hm := mul_le_mul_of_nonneg_left hsum (mul_nonneg ha0.le hK0)
  have hscalar : a0*N = 1/X := (eq_div_iff hX.ne').mpr hnorm
  have he : a0*K0*(N*B) = K0*K1*Real.exp (-s/96)+K0*err/X := by
    dsimp [B]
    calc
      _ = (a0*N*X)*(K0*K1*Real.exp (-s/96))+(a0*N)*(K0*err) := by ring
      _ = _ := by rw [hnorm,hscalar];ring
  have her : 0 ≤ err := by dsimp [err] <;> positivity
  have hlast : K0*err/X ≤ err/X := div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK01 her) hX.le
  have hright : err/X = 4*(H.divisors.card : ℝ)*(H : ℝ)/
      (modelLength R xi (H : ℝ) (C0 : ℝ)*(H.totient : ℝ))*(w^s)^2 := by
    dsimp [err,X,Y]
    field_simp
  rw [hbase]
  exact hm.trans (he ▸ add_le_add le_rfl (hlast.trans_eq hright))

end ErdosVarianceMoments



end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosVarianceMoments.finite_joint_moment_estimate_jb247_oai := @OAI.Erdos970.ErdosVarianceMoments.finite_joint_moment_estimate_jb247_oai
