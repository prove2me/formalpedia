-- Prove2me | solution 1 for OAI.Erdos970.ErdosInverseFrozen.frozen_exceptional_mean_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:50.575054+00:00
-- url     : https://prove2.me/submissions/241d487d-fcc9-4e38-a55a-532aeac63405

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
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
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
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J007

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReducedFractions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
open scoped BigOperators

namespace AdditiveLargeSieve

theorem fractionValue_mem {Q : ℕ} {z : ℕ × ℕ} (hz : z ∈ reducedFractions Q) :
    fractionValue z ∈ Ico (0 : ℝ) 1 := by
  rcases mem_reducedFractions.mp hz with ⟨hq, _, ha, _⟩
  have hq' : 0 < (z.1 : ℝ) := by exact_mod_cast (show 0 < z.1 by omega)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq'.le,
    (div_lt_one hq').2 (by exact_mod_cast ha)⟩

theorem reduced_cross_injective {x y : ℕ × ℕ}
    (_hx : 0 < x.1) (hy : 0 < y.1) (hcx : x.2.Coprime x.1) (hcy : y.2.Coprime y.1)
    (h : x.2 * y.1 = y.2 * x.1) : x = y := by
  have hxy : x.1 ∣ y.1 := hcx.symm.dvd_of_dvd_mul_left (h ▸ Nat.dvd_mul_left x.1 y.2)
  have hyx : y.1 ∣ x.1 := hcy.symm.dvd_of_dvd_mul_left (h.symm ▸ Nat.dvd_mul_left y.1 x.2)
  have hq : x.1 = y.1 := Nat.dvd_antisymm hxy hyx
  have ha : x.2 = y.2 := by
    rw [hq] at h
    exact Nat.eq_of_mul_eq_mul_right hy h
  exact Prod.ext hq ha

theorem one_le_abs_cast_sub {a b : ℕ} (hab : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem reduced_fraction_separation {Q : ℕ} (hQ : 0 < Q)
    {x y : ℕ × ℕ} (hx : x ∈ reducedFractions Q) (hy : y ∈ reducedFractions Q) (hne : x ≠ y) :
    ((Q : ℝ) ^ 2)⁻¹ ≤ |fractionValue x - fractionValue y| := by
  rcases mem_reducedFractions.mp hx with ⟨hx0, hxQ, _, hcx⟩
  rcases mem_reducedFractions.mp hy with ⟨hy0, hyQ, _, hcy⟩
  have hxpos : 0 < (x.1 : ℝ) := by exact_mod_cast (show 0 < x.1 by omega)
  have hypos : 0 < (y.1 : ℝ) := by exact_mod_cast (show 0 < y.1 by omega)
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hcross : x.2 * y.1 ≠ y.2 * x.1 := by
    intro h
    exact hne (reduced_cross_injective (by omega) (by omega) hcx hcy h)
  have hnum := one_le_abs_cast_sub hcross
  simp only [Nat.cast_mul] at hnum
  have hformula : fractionValue x - fractionValue y =
      ((x.2 : ℝ) * y.1 - y.2 * x.1) / ((x.1 : ℝ) * y.1) := by
    dsimp [fractionValue]
    field_simp
  rw [hformula, abs_div, abs_of_pos (mul_pos hxpos hypos)]
  have hprod : (x.1 : ℝ) * y.1 ≤ (Q : ℝ) ^ 2 := by
    have hxQ' : (x.1 : ℝ) ≤ Q := by exact_mod_cast hxQ
    have hyQ' : (y.1 : ℝ) ≤ Q := by exact_mod_cast hyQ
    nlinarith
  calc
    ((Q : ℝ) ^ 2)⁻¹ = 1 / (Q : ℝ) ^ 2 := by rw [one_div]
    _ ≤ 1 / ((x.1 : ℝ) * y.1) := one_div_le_one_div_of_le (mul_pos hxpos hypos) hprod
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hxpos hypos).le

theorem sum_reducedFractions {E : Type*} [AddCommMonoid E] (Q : ℕ) (f : ℕ × ℕ → E) :
    ∑ z ∈ reducedFractions Q, f z =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f (q, a) := by
  classical
  simp only [reducedFractions, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  have hsets : (Finset.range Q).filter (fun a => a < q ∧ a.Coprime q) =
      (Finset.range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    have := (Finset.mem_Icc.mp hq).2
    omega
  rw [hsets, Finset.sum_filter]

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SeparatedSampling
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
open scoped BigOperators

namespace AdditiveLargeSieve

theorem endpoint_sample {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x) {a δ : ℝ} (hδ : 0 < δ) :
    δ * f a ≤ (∫ x in a..a + δ, f x) + δ * ∫ x in a..a + δ, |f' x| := by
  have hab : a ≤ a + δ := by linarith
  have hpoint (t : ℝ) (ht : t ∈ Icc a (a + δ)) :
      f a ≤ f t + ∫ x in a..a + δ, |f' x| := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (hf'.intervalIntegrable a t)
    have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f') ht.1
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := fun x => |f' x|)
      (le_refl a) ht.1 ht.2 (Filter.Eventually.of_forall fun x => abs_nonneg (f' x))
      (hf'.abs.intervalIntegrable a (a + δ))
    rw [hftc] at hnorm
    have := neg_le_abs (f t - f a)
    linarith
  have hint := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (μ := volume) (c := f a))
    ((hf.add continuous_const).intervalIntegrable a (a + δ)) hpoint
  simp only [Pi.add_apply] at hint
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const] at hint
  simpa only [add_sub_cancel_left, smul_eq_mul] using hint

theorem disjoint_sample_intervals {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|) :
    Set.Pairwise (↑s) (fun i j => Disjoint (Ioc (t i) (t i + δ))
      (Ioc (t j) (t j + δ))) := by
  intro i hi j hj hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h := hsep i hi j hj hij
  rcases le_abs.mp h with h | h <;> linarith [hxi.1, hxi.2, hxj.1, hxj.2]

theorem sum_local_integrals_le {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {δ L U : ℝ} (hδ : 0 < δ) (hLU : L ≤ U)
    (hinside : ∀ i ∈ s, L ≤ t i ∧ t i + δ ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ s, ∫ x in t i..t i + δ, f x) ≤ ∫ x in L..U, f x := by
  have hle (i : ι) : t i ≤ t i + δ := by linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  rw [← integral_biUnion_finset s (fun _ _ => measurableSet_Ioc)
    (disjoint_sample_intervals hsep) (fun i _ => (hf.intervalIntegrable _ _).1),
    intervalIntegral.integral_of_le hLU]
  apply setIntegral_mono_set (hf.intervalIntegrable L U).1
    (Filter.Eventually.of_forall hpos)
  exact Filter.Eventually.of_forall fun x hx => by
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact ⟨lt_of_le_of_lt (hinside i hi).1 hxi.1, hxi.2.trans (hinside i hi).2⟩

theorem separated_sampling {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {δ L U : ℝ} (hδ : 0 < δ) (hLU : L ≤ U)
    (hinside : ∀ i ∈ s, L ≤ t i ∧ t i + δ ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ s, f (t i)) ≤
      δ⁻¹ * (∫ x in L..U, f x) + ∫ x in L..U, |f' x| := by
  have hlocal := Finset.sum_le_sum (s := s) fun i _ => endpoint_sample hf hf' hderiv
    (a := t i) hδ
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hlocal
  have hfbound := sum_local_integrals_le s t hδ hLU hinside hsep hf hpos
  have hdbound := sum_local_integrals_le s t hδ hLU hinside hsep hf'.abs
    (fun x => abs_nonneg (f' x))
  have hbound : δ * (∑ i ∈ s, f (t i)) ≤
      (∫ x in L..U, f x) + δ * ∫ x in L..U, |f' x| :=
    hlocal.trans (add_le_add hfbound (mul_le_mul_of_nonneg_left hdbound hδ.le))
  calc
    (∑ i ∈ s, f (t i)) ≤ ((∫ x in L..U, f x) +
        δ * ∫ x in L..U, |f' x|) / δ := (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hbound)
    _ = _ := by field_simp

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_HyperbolaFourier
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

theorem integerWeight_orthogonality (N : ℕ) [NeZero N] (I : Finset ℤ) (u : ZMod N) :
    (∑ h : ZMod N, integerWeight N I h * ZMod.stdAddChar (h*u)) =
      (N : ℂ) * (integerFibre N I u).card := by
  unfold integerWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (h : ZMod N) (x : ℤ) :
      ZMod.stdAddChar (-h*(x : ZMod N)) * ZMod.stdAddChar (h*u) =
        ZMod.stdAddChar (h*(u-(x : ZMod N))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  have he (x : ℤ) : u-(x : ZMod N) = 0 ↔ (x : ZMod N) = u := by
    rw [sub_eq_zero, eq_comm]
  simp_rw [he]
  simp only [ZMod.card, apply_ite, Nat.cast_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, integerFibre]
  ring

end ErdosHyperbolaIdentities

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

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseHits

theorem mem_frozenCoordinates (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) (j : ℕ) :
    j ∈ frozenCoordinates N w p q b v a ↔ j < N ∧
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        ¬Int.ModEq (t : ℤ) (b+(q : ℤ)*(v+(p : ℤ)*j)) (a t : ℤ) := by
  rw [frozenCoordinates,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors]
  simp only [Finset.mem_range,ProgressionSmallSieve.progressionHit,Nat.cast_mul]
  have heq : b+(q : ℤ)*v+(p : ℤ)*q*j = b+(q : ℤ)*(v+(p : ℤ)*j) := by ring
  rw [heq]

end ErdosInverseFrozen

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_FourierDerivative
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

theorem monomial_continuous (n : ℤ) : Continuous (monomial n) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' 1)

theorem polynomial_continuous (s : Finset ℤ) (b : ℤ → ℂ) : Continuous (polynomial s b) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (monomial_continuous n)

theorem unit_monomial_integral (n : ℤ) (a : ℝ) :
    (∫ x in a..a + 1, monomial n x) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  rw [fourierCoeff_eq_intervalIntegral _ _ a] at h
  simpa [monomial, Pi.single_apply, eq_comm] using h

theorem monomial_conj_mul (n m : ℤ) (x : ℝ) :
    conj (monomial n x) * monomial m x = monomial (m - n) x := by
  simp only [monomial, ← fourier_neg, ← fourier_add]
  congr 2
  omega

theorem polynomial_square_expansion (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    conj (polynomial s b x) * polynomial s b x =
      ∑ n ∈ s, ∑ m ∈ s, (conj (b n) * b m) * monomial (m - n) x := by
  simp only [polynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [← monomial_conj_mul]
  ring

theorem polynomial_energy (s : Finset ℤ) (b : ℤ → ℂ) (a : ℝ) :
    (∫ x in a..a + 1, ‖polynomial s b x‖ ^ 2) = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have h : (∫ x in a..a + 1, conj (polynomial s b x) * polynomial s b x) =
      ∑ n ∈ s, conj (b n) * b n := by
    simp_rw [polynomial_square_expansion]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, unit_monomial_integral]
        simp [sub_eq_zero, hn]
      · intro m _
        exact (continuous_const.mul (monomial_continuous _)).intervalIntegrable _ _
    · intro n _
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ fun m _ => continuous_const.mul (monomial_continuous _)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_sum] using h

theorem polynomial_energy_two (s : Finset ℤ) (b : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..2, ‖polynomial s b x‖ ^ 2) = 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have hc := (polynomial_continuous s b).norm.pow 2
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 2)
  simp only [Pi.pow_apply] at hsum
  have h0 := polynomial_energy s b 0
  have h1 := polynomial_energy s b 1
  norm_num only [zero_add, one_add_one_eq_two] at h0 h1
  linarith

end AdditiveLargeSieve

end

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate RealInnerProductSpace

namespace AdditiveLargeSieve

theorem polynomial_hasDerivAt (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (polynomial s b) (polynomial s (derivativeCoefficients b) x) x := by
  have h := HasDerivAt.fun_sum (u := s) fun n _ =>
    (hasDerivAt_fourier (1 : ℝ) n x).const_mul (b n)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [polynomial, derivativeCoefficients, Complex.ofReal_one, div_one, monomial]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem derivative_coefficient_norm (b : ℤ → ℂ) (n : ℤ) :
    ‖derivativeCoefficients b n‖ = 2 * Real.pi * |(n : ℝ)| * ‖b n‖ := by
  simp [derivativeCoefficients, Complex.norm_intCast, Real.pi_nonneg]

theorem derivative_energy_le (s : Finset ℤ) (b : ℤ → ℂ) {R : ℝ} (hR : 0 < R)
    (hfreq : ∀ n ∈ s, |(n : ℝ)| ≤ R) :
    (∫ x in (0 : ℝ)..2, ‖polynomial s (derivativeCoefficients b) x‖ ^ 2) ≤
      2 * (2 * Real.pi * R) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  rw [polynomial_energy_two, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [derivative_coefficient_norm]
  have h : 2 * Real.pi * |(n : ℝ)| * ‖b n‖ ≤ 2 * Real.pi * R * ‖b n‖ := by
    gcongr
    exact hfreq n hn
  have hnonneg : 0 ≤ 2 * Real.pi * |(n : ℝ)| * ‖b n‖ := by positivity
  have hnonneg' : 0 ≤ 2 * Real.pi * R * ‖b n‖ := by positivity
  nlinarith [sq_le_sq₀ hnonneg hnonneg' |>.2 h]

theorem norm_square_derivative_bound (z w : ℂ) {R : ℝ} (hR : 0 < R) :
    |2 * inner ℝ z w| ≤ R * ‖z‖ ^ 2 + R⁻¹ * ‖w‖ ^ 2 := by
  calc
    |2 * inner ℝ z w| = 2 * |inner ℝ z w| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (‖z‖ * ‖w‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z w) (by norm_num)
    _ ≤ _ := by
      apply (mul_le_mul_iff_right₀ hR).mp
      field_simp
      nlinarith [sq_nonneg (R * ‖z‖ - ‖w‖)]

theorem separated_polynomial_bound {ι : Type*} (samples : Finset ι) (t : ι → ℝ)
    (s : Finset ℤ) (b : ℤ → ℂ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpoints : ∀ i ∈ samples, t i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i ∈ samples, ∀ j ∈ samples, i ≠ j → δ ≤ |t i - t j|)
    (hfreq : ∀ n ∈ s, |(n : ℝ)| ≤ R) :
    (∑ i ∈ samples, ‖polynomial s b (t i)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * (R + δ⁻¹) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  let F := polynomial s b
  let D := polynomial s (derivativeCoefficients b)
  have hF : Continuous F := polynomial_continuous s b
  have hD : Continuous D := polynomial_continuous s _
  have hsample := separated_sampling samples t hδ (by norm_num : (0 : ℝ) ≤ 2)
    (fun i hi => ⟨(hpoints i hi).1, by linarith [(hpoints i hi).2]⟩) hsep
    (hF.norm.pow 2) ((continuous_const.mul (hF.inner hD)) : Continuous (fun x => 2 * inner ℝ (F x) (D x)))
    (fun x => (polynomial_hasDerivAt s b x).norm_sq) (fun x => sq_nonneg ‖F x‖)
  have hderiv : (∫ x in (0 : ℝ)..2, |2 * inner ℝ (F x) (D x)|) ≤
      R * (∫ x in (0 : ℝ)..2, ‖F x‖ ^ 2) + R⁻¹ * (∫ x in (0 : ℝ)..2, ‖D x‖ ^ 2) := by
    have h := intervalIntegral.integral_mono (μ := volume) (by norm_num : (0 : ℝ) ≤ 2)
      ((continuous_const.mul (hF.inner hD)).abs.intervalIntegrable 0 2)
      (((continuous_const.mul (hF.norm.pow 2)).add
        (continuous_const.mul (hD.norm.pow 2))).intervalIntegrable 0 2)
      (fun x => norm_square_derivative_bound (F x) (D x) hR)
    have hiF : IntervalIntegrable (fun x => R * ‖F x‖ ^ 2) volume 0 2 :=
      (continuous_const.mul (hF.norm.pow 2)).intervalIntegrable _ _
    have hiD : IntervalIntegrable (fun x => R⁻¹ * ‖D x‖ ^ 2) volume 0 2 :=
      (continuous_const.mul (hD.norm.pow 2)).intervalIntegrable _ _
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at h
    rw [intervalIntegral.integral_add hiF hiD,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hE : (∫ x in (0 : ℝ)..2, ‖F x‖ ^ 2) = 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := polynomial_energy_two s b
  have hDE := derivative_energy_le s b hR hfreq
  have hEpos : 0 ≤ ∑ n ∈ s, ‖b n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  simp only [Pi.pow_apply, Pi.mul_apply] at hsample
  have hfinal := hsample.trans (add_le_add le_rfl hderiv)
  rw [hE] at hfinal
  have hbound := mul_le_mul_of_nonneg_left hDE (inv_nonneg.mpr hR.le)
  have halgebra : δ⁻¹ * (2 * ∑ n ∈ s, ‖b n‖ ^ 2) +
      (R * (2 * ∑ n ∈ s, ‖b n‖ ^ 2) + R⁻¹ *
        (2 * (2 * Real.pi * R) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2)) =
      (2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
    field_simp
    ring
  have hc : 2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R ≤
      (4 + 8 * Real.pi ^ 2) * (R + δ⁻¹) := by
    have := mul_nonneg (sq_nonneg Real.pi) (inv_nonneg.mpr hδ.le)
    have := inv_nonneg.mpr hδ.le
    nlinarith
  have hjoin : (∑ i ∈ samples, ‖F (t i)‖ ^ 2) ≤
      (2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
    rw [← halgebra]
    exact hfinal.trans (add_le_add le_rfl (add_le_add le_rfl hbound))
  exact hjoin.trans (mul_le_mul_of_nonneg_right hc hEpos)

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerResidueVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

theorem monomial_eq_exponential (n : ℤ) (x : ℝ) :
    monomial n x = exponential ((n : ℝ) * x) := by
  rw [monomial, fourier_coe_apply]
  simp only [exponential, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

theorem monomial_add (m n : ℤ) (x : ℝ) :
    monomial (m + n) x = monomial m x * monomial n x := fourier_add

theorem monomial_norm (n : ℤ) (x : ℝ) : ‖monomial n x‖ = 1 := by
  exact Circle.norm_coe _

theorem shifted_sum_norm (J : ℕ) (M : ℤ) (b : ℕ → ℂ) (x : ℝ) :
    ‖∑ j ∈ Finset.range J, b j * exponential (((M + (j : ℤ) : ℤ) : ℝ) * x)‖ =
      ‖∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x‖ := by
  simp_rw [← monomial_eq_exponential]
  have h : (∑ j ∈ Finset.range J, b j * monomial (M + (j : ℤ)) x) =
      monomial M x * ∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [monomial_add]
    ring
  rw [h, norm_mul, monomial_norm, one_mul]

theorem separated_consecutive_bound {ι : Type*} (samples : Finset ι) (t : ι → ℝ)
    (J : ℕ) (M : ℤ) (b : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpoints : ∀ i ∈ samples, t i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i ∈ samples, ∀ j ∈ samples, i ≠ j → δ ≤ |t i - t j|) :
    (∑ i ∈ samples, ‖∑ j ∈ Finset.range J,
      b j * exponential (((M + (j : ℤ) : ℤ) : ℝ) * t i)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * ((J : ℝ) + δ⁻¹) * ∑ j ∈ Finset.range J, ‖b j‖ ^ 2 := by
  by_cases hJ : J = 0
  · simp [hJ]
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  let s : Finset ℤ := (Finset.range J).image (fun j : ℕ => (j : ℤ))
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := Int.ofNat_injective
  have hf (n : ℤ) (hn : n ∈ s) : |(n : ℝ)| ≤ (J : ℝ) := by
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    have hj' := Finset.mem_range.mp hj
    norm_cast
    omega
  have h := separated_polynomial_bound samples t s (fun n => b n.toNat)
    hJpos hδ hδ1 hpoints hsep hf
  have hp (x : ℝ) : polynomial s (fun n => b n.toNat) x =
      ∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x := by
    rw [polynomial, Finset.sum_image hinj.injOn]
    simp
  have he : (∑ n ∈ s, ‖b n.toNat‖ ^ 2) = ∑ j ∈ Finset.range J, ‖b j‖ ^ 2 := by
    rw [Finset.sum_image hinj.injOn]
    simp
  simp_rw [hp] at h
  rw [he] at h
  simpa only [shifted_sum_norm] using h

theorem additive_large_sieve (Q J : ℕ) (M : ℤ) (b : ℤ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      ‖∑ j ∈ Finset.range J, b (M + (j : ℤ)) *
        exponential ((((M + (j : ℤ) : ℤ) : ℝ) * a) / q)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * ((J : ℝ) + (Q : ℝ) ^ 2) *
        ∑ j ∈ Finset.range J, ‖b (M + (j : ℤ))‖ ^ 2 := by
  by_cases hQ : Q = 0
  · simp only [hQ, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    positivity
  have hQpos : 0 < Q := by omega
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
  have hdelta : 0 < ((Q : ℝ) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hQreal)
  have hdelta1 : ((Q : ℝ) ^ 2)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (sq_pos_of_pos hQreal)).2
    nlinarith
  have h := separated_consecutive_bound (reducedFractions Q) fractionValue J M
    (fun j => b (M + (j : ℤ))) hdelta hdelta1
    (fun _ hz => ⟨(fractionValue_mem hz).1, (fractionValue_mem hz).2.le⟩)
    (fun _ hx _ hy hne => reduced_fraction_separation hQpos hx hy hne)
  rw [sum_reducedFractions] at h
  simpa only [fractionValue, inv_inv, mul_div_assoc] using h

end AdditiveLargeSieve

end

section

open scoped ComplexConjugate
namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

theorem spectrum_eq_sum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    spectrum N S a = ∑ x ∈ S,ZMod.stdAddChar (a*(x : ZMod N)) := by
  simp only [spectrum,integerWeight,neg_neg]

theorem spectrum_zero (N : ℕ) [NeZero N] (S : Finset ℤ) : spectrum N S 0 = (S.card : ℂ) := by
  simp [spectrum,integerWeight]

theorem spectrum_orthogonality (N : ℕ) [NeZero N] (S : Finset ℤ) (e : ZMod N) :
    (∑ a : ZMod N,spectrum N S a*ZMod.stdAddChar (-a*e)) = (N : ℂ)*(residueCount N S e : ℂ) := by
  have he : (∑ a : ZMod N,integerWeight N S (-a)*ZMod.stdAddChar ((-a)*e)) =
      ∑ a : ZMod N,integerWeight N S a*ZMod.stdAddChar (a*e) :=
    Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)
  exact he.trans (integerWeight_orthogonality N S e)

theorem conjugate_spectrum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    conj (spectrum N S a) = ∑ x ∈ S,ZMod.stdAddChar (-a*(x : ZMod N)) := by
  rw [spectrum_eq_sum,map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  ring

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

theorem residue_weighted_sum {R : Type*} [CommSemiring R] (N : ℕ) [NeZero N]
    (S : Finset ℤ) (f : ZMod N → R) :
    (∑ e : ZMod N,f e*(residueCount N S e : R)) = ∑ x ∈ S,f (x : ZMod N) := by
  calc
    _ = ∑ e : ZMod N,∑ _x ∈ integerFibre N S e,f e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [residueCount,mul_comm]
    _ = ∑ e : ZMod N,∑ x ∈ S,if (x : ZMod N) = e then f e else 0 := by
      simp only [integerFibre,Finset.sum_filter]
    _ = ∑ x ∈ S,∑ e : ZMod N,if (x : ZMod N) = e then f e else 0 := Finset.sum_comm
    _ = _ := by simp

theorem residue_count_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ e : ZMod N,residueCount N S e) = S.card := by
  have hh := residue_weighted_sum (R := ℕ) N S (fun _ => 1)
  simpa only [Nat.cast_id,one_mul,Finset.sum_const,nsmul_eq_mul,mul_one] using hh

theorem residue_square_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ x ∈ S,residueCount N S (x : ZMod N)) = ∑ e : ZMod N,(residueCount N S e)^2 := by
  simpa only [Nat.cast_id,pow_two] using (residue_weighted_sum (R := ℕ) N S (residueCount N S)).symm

end ErdosInverseSpectrum

end

section

open scoped ComplexConjugate
namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem spectrum_conjugate_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ a : ZMod N,spectrum N S a*conj (spectrum N S a)) =
      (N : ℂ)*∑ e : ZMod N,(residueCount N S e : ℂ)^2 := by
  have hf : (∑ x ∈ S,(residueCount N S (x : ZMod N) : ℂ)) =
      ∑ e : ZMod N,(residueCount N S e : ℂ)^2 := by
    exact_mod_cast residue_square_sum N S
  calc
    _ = ∑ a : ZMod N,∑ x ∈ S,spectrum N S a*ZMod.stdAddChar (-a*(x : ZMod N)) := by
      simp_rw [conjugate_spectrum,Finset.mul_sum]
    _ = ∑ x ∈ S,∑ a : ZMod N,spectrum N S a*ZMod.stdAddChar (-a*(x : ZMod N)) := Finset.sum_comm
    _ = ∑ x ∈ S,(N : ℂ)*(residueCount N S (x : ZMod N) : ℂ) :=
      Finset.sum_congr rfl (fun x _ => spectrum_orthogonality N S (x : ZMod N))
    _ = (N : ℂ)*(∑ x ∈ S,(residueCount N S (x : ZMod N) : ℂ)) := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [hf]

theorem spectrum_parseval (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ a : ZMod N,‖spectrum N S a‖^2) = (N : ℝ)*∑ e : ZMod N,(residueCount N S e : ℝ)^2 := by
  have hh := spectrum_conjugate_sum N S
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at hh
  exact_mod_cast hh

theorem centered_residue_variance (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod N)),‖spectrum N S a‖^2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsum : (∑ e : ZMod N,(residueCount N S e : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast residue_count_sum N S
  have hcenter : (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      (N : ℝ)*(∑ e : ZMod N,(residueCount N S e : ℝ)^2)-(S.card : ℝ)^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hcross : (∑ e : ZMod N,2*(residueCount N S e : ℝ)*((S.card : ℝ)/(N : ℝ))) =
        2*(S.card : ℝ)*((S.card : ℝ)/(N : ℝ)) := by
      rw [← Finset.sum_mul,← Finset.mul_sum,hsum]
    rw [hcross]
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    field_simp
    ring
  have hzero : ‖spectrum N S (0 : ZMod N)‖^2 = (S.card : ℝ)^2 := by
    rw [spectrum_zero]
    norm_num
  have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun a => ‖spectrum N S a‖^2) (Finset.mem_univ (0 : ZMod N))
  rw [hzero,spectrum_parseval] at he
  rw [hcenter]
  linarith

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem spectrum_eq_exponentialSum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ℕ) :
    spectrum N S (a : ZMod N) = exponentialSum S a N := by
  rw [spectrum_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have he : (a : ZMod N)*(x : ZMod N) = (((a : ℤ)*x : ℤ) : ZMod N) := by
    simp only [Int.cast_mul,Int.cast_natCast]
  rw [he,ZMod.stdAddChar_coe]
  unfold AdditiveLargeSieve.exponential
  congr 1
  push_cast
  ring

theorem spectrum_eq_exponentialSum_val (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    spectrum N S a = exponentialSum S a.val N := by
  simpa only [ZMod.natCast_zmod_val] using spectrum_eq_exponentialSum N S a.val

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem residue_values_univ (N : ℕ) [NeZero N] :
    (Finset.univ : Finset (ZMod N)).image ZMod.val = Finset.range N := by
  ext a
  constructor
  · intro ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (ZMod.val_lt r)
  · intro ha
    exact Finset.mem_image.mpr ⟨(a : ZMod N),Finset.mem_univ _,ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)⟩

theorem sum_over_residues (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ e : ZMod N,f e.val) = ∑ e ∈ Finset.range N,f e := by
  rw [← residue_values_univ N,Finset.sum_image]
  intro a ha b hb hab
  exact ZMod.val_injective N hab

theorem residue_values_nonzero (N : ℕ) [NeZero N] :
    ((Finset.univ : Finset (ZMod N)).erase 0).image ZMod.val = (Finset.range N).erase 0 := by
  ext a
  constructor
  · intro ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hr0,hrU⟩ := Finset.mem_erase.mp hr
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_range.mpr (ZMod.val_lt r)⟩
    intro hz
    apply hr0
    apply ZMod.val_injective N
    simpa only [ZMod.val_zero] using hz
  · intro ha
    obtain ⟨ha0,haN⟩ := Finset.mem_erase.mp ha
    have haval := ZMod.val_natCast_of_lt (Finset.mem_range.mp haN)
    have har : (a : ZMod N) ≠ 0 := by
      intro hh
      have hval := congrArg ZMod.val hh
      rw [haval,ZMod.val_zero] at hval
      exact ha0 hval
    exact Finset.mem_image.mpr ⟨(a : ZMod N),Finset.mem_erase.mpr ⟨har,Finset.mem_univ _⟩,haval⟩

theorem sum_over_nonzero_residues (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ e ∈ (Finset.univ.erase (0 : ZMod N)),f e.val) = ∑ e ∈ (Finset.range N).erase 0,f e := by
  rw [← residue_values_nonzero N,Finset.sum_image]
  intro a ha b hb hab
  exact ZMod.val_injective N hab

theorem centered_variance_exponential (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      ∑ a ∈ (Finset.range N).erase 0,‖exponentialSum S a N‖^2 := by
  rw [centered_residue_variance]
  simp_rw [spectrum_eq_exponentialSum_val]
  exact sum_over_nonzero_residues N (fun a => ‖exponentialSum S a N‖^2)

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

theorem residueCount_at_val (N : ℕ) [NeZero N] (S : Finset ℤ) (e : ZMod N) :
    residueCount N S e = integerResidueCount N S e.val := by
  unfold residueCount integerResidueCount
  congr 1
  ext x
  simp only [integerFibre,Finset.mem_filter]
  apply and_congr_right
  intro _hx
  rw [← ZMod.val_intCast x]
  constructor
  · intro he
    rw [he]
  · intro he
    exact ZMod.val_injective N (Int.ofNat_inj.mp he)

theorem variance_eq_integerResidueVariance (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) = integerResidueVariance N S := by
  simp_rw [residueCount_at_val]
  exact sum_over_residues N (fun e => ((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2)

theorem integer_variance_fourier (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*integerResidueVariance N S = ∑ a ∈ (Finset.range N).erase 0,‖exponentialSum S a N‖^2 := by
  rw [← variance_eq_integerResidueVariance]
  exact centered_variance_exponential N S

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalSpectrumCoefficients
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem intervalCoordinates_image (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) :
    (intervalCoordinates S M J).image (fun j : ℕ => M+(j : ℤ)) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hj).2
  · intro hx
    have hr := Finset.mem_Ico.mp (hS hx)
    let j := (x-M).toNat
    have he : (j : ℤ) = x-M := Int.toNat_of_nonneg (by omega)
    have hj : j < J := by
      have hh : (j : ℤ) < (J : ℤ) := by rw [he];omega
      exact_mod_cast hh
    have hpoint : M+(j : ℤ) = x := by rw [he];ring
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hpoint.symm ▸ hx⟩,hpoint⟩

theorem intervalCoordinates_card (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) : (intervalCoordinates S M J).card = S.card := by
  have hi : Function.Injective (fun j : ℕ => M+(j : ℤ)) :=
    fun _ _ h => Int.ofNat_injective (add_left_cancel h)
  have hc := Finset.card_image_of_injective (intervalCoordinates S M J) hi
  exact hc.symm.trans (congrArg Finset.card (intervalCoordinates_image S M J hS))

theorem indicator_weighted_sum (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (f : ℤ → ℂ) :
    (∑ j ∈ Finset.range J,indicatorCoefficient S (M+(j : ℤ))*f (M+(j : ℤ))) = ∑ x ∈ S,f x := by
  have hi : Function.Injective (fun j : ℕ => M+(j : ℤ)) :=
    fun _ _ h => Int.ofNat_injective (add_left_cancel h)
  simp only [indicatorCoefficient,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter]
  change (∑ j ∈ intervalCoordinates S M J,f (M+(j : ℤ))) = ∑ x ∈ S,f x
  calc
    _ = ∑ x ∈ (intervalCoordinates S M J).image (fun j : ℕ => M+(j : ℤ)),f x :=
      (Finset.sum_image hi.injOn).symm
    _ = _ := congrArg (fun V : Finset ℤ => ∑ x ∈ V,f x) (intervalCoordinates_image S M J hS)

theorem indicator_energy (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) :
    (∑ j ∈ Finset.range J,‖indicatorCoefficient S (M+(j : ℤ))‖^2) = (S.card : ℝ) := by
  have he (x : ℤ) : ‖indicatorCoefficient S x‖^2 = if x ∈ S then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ S <;> simp [indicatorCoefficient,hx]
  simp_rw [he]
  rw [Finset.sum_boole]
  change ((intervalCoordinates S M J).card : ℝ) = S.card
  rw [intervalCoordinates_card S M J hS]

theorem indicator_exponential_sum (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (a q : ℕ) :
    (∑ j ∈ Finset.range J,indicatorCoefficient S (M+(j : ℤ))*
      AdditiveLargeSieve.exponential ((((M+(j : ℤ) : ℤ) : ℝ)*(a : ℝ))/(q : ℝ))) =
        exponentialSum S a q :=
  indicator_weighted_sum S M J hS (fun x => AdditiveLargeSieve.exponential (((x : ℝ)*(a : ℝ))/(q : ℝ)))

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PrimeFourierSieve
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem prime_reduced_residues (p : ℕ) (hp : Nat.Prime p) :
    (Finset.range p).erase 0 = (Finset.range p).filter (fun a => Nat.Coprime a p) := by
  ext a
  simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_filter]
  constructor
  · rintro ⟨ha0,hap⟩
    refine ⟨hap,?_⟩
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hd
    exact (not_le_of_gt hap) (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hd)
  · rintro ⟨hap,hcop⟩
    refine ⟨?_,hap⟩
    intro ha0
    subst a
    have hh : p = 1 := by simpa using hcop
    exact hp.ne_one hh

theorem prime_variance_large_sieve (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) :
    (∑ p ∈ P,(p : ℝ)*integerResidueVariance p S) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ) := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (p : ℝ)*integerResidueVariance p S =
        ∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 := by
    let : NeZero p := ⟨(hP p hp).ne_zero⟩
    rw [integer_variance_fourier,prime_reduced_residues p (hP p hp)]
  have hsub : P ⊆ Finset.Icc 1 Q := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).one_le,hQ p hp⟩
  have hals := AdditiveLargeSieve.additive_large_sieve Q J M (indicatorCoefficient S)
  simp_rw [indicator_exponential_sum S M J hS] at hals
  rw [indicator_energy S M J hS] at hals
  calc
    _ = ∑ p ∈ P,∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 :=
      Finset.sum_congr rfl hpoint
    _ ≤ ∑ p ∈ Finset.Icc 1 Q,∑ a ∈ (Finset.range p).filter (fun a => a.Coprime p),‖exponentialSum S a p‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ _ := hals

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExceptionalResidues
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

theorem exceptionalResidues_card (N : ℕ) (S : Finset ℤ) (T : ℝ) :
    (exceptionalResidues N S T).card = (deviationResidues N S T).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have haN := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hbN := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt haN,ZMod.val_natCast_of_lt hbN] using hh

theorem exceptional_fraction_le_variance (N : ℕ) (hN : 0 < N) (S : Finset ℤ) (T : ℝ) (hT : 0 < T) :
    ((exceptionalResidues N S T).card : ℝ)/(N : ℝ) ≤
      (N : ℝ)*integerResidueVariance N S/T^2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hthreshold : 0 ≤ T/(N : ℝ) := (div_pos hT hNR).le
  have hsum : ((deviationResidues N S T).card : ℝ)*(T/(N : ℝ))^2 ≤ integerResidueVariance N S := by
    calc
      _ = ∑ _e ∈ deviationResidues N S T,(T/(N : ℝ))^2 := by simp
      _ ≤ ∑ e ∈ deviationResidues N S T,((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro e he
        have hh := (Finset.mem_filter.mp he).2
        calc
          _ ≤ |(integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ)|^2 :=
            pow_le_pow_left₀ hthreshold hh.le 2
          _ = _ := sq_abs _
      _ ≤ integerResidueVariance N S :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  rw [exceptionalResidues_card]
  apply (div_le_div_iff₀ hNR (sq_pos_of_pos hT)).mpr
  calc
    _ = (((deviationResidues N S T).card : ℝ)*(T/(N : ℝ))^2)*(N : ℝ)^2 := by field_simp
    _ ≤ integerResidueVariance N S*(N : ℝ)^2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by ring

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeExceptionalMean
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem exceptional_fraction_sum_bound (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) (T : ℝ) (hT : 0 < T) :
    (∑ p ∈ P,((exceptionalResidues p S T).card : ℝ)/(p : ℝ)) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/T^2 := by
  calc
    _ ≤ ∑ p ∈ P,((p : ℝ)*integerResidueVariance p S)/T^2 :=
      Finset.sum_le_sum (fun p hp => exceptional_fraction_le_variance p (hP p hp).pos S T hT)
    _ = (∑ p ∈ P,(p : ℝ)*integerResidueVariance p S)/T^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (prime_variance_large_sieve P hP Q J M S hS hQ) (sq_nonneg _)

theorem exceptional_fraction_average_bound (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (hn : 0 < P.card) (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) (T : ℝ) (hT : 0 < T) :
    (∑ p ∈ P,((exceptionalResidues p S T).card : ℝ)/(p : ℝ))/(P.card : ℝ) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/((P.card : ℝ)*T^2) := by
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  calc
    _ ≤ ((4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/T^2)/(P.card : ℝ) :=
      div_le_div_of_nonneg_right (exceptional_fraction_sum_bound P hP Q J M S hS hQ T hT) hnR.le
    _ = _ := by ring

theorem exceptional_average_of_survivor_upper (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (hn : 0 < P.card) (Q J : ℕ) (hJ : 0 < J) (M : ℤ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (hQ : ∀ p ∈ P,p ≤ Q)
    (delta V0 C : ℝ) (hd : 0 < delta) (hV : 0 < V0)
    (hm : (S.card : ℝ) ≤ C*(J : ℝ)*V0) :
    (∑ p ∈ P,((exceptionalResidues p S (delta*(J : ℝ)*V0)).card : ℝ)/(p : ℝ))/(P.card : ℝ) ≤
      (4+8*Real.pi^2)*C*((J : ℝ)+(Q : ℝ)^2)/((P.card : ℝ)*delta^2*(J : ℝ)*V0) := by
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hT : 0 < delta*(J : ℝ)*V0 := mul_pos (mul_pos hd hJR) hV
  calc
    _ ≤ (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/
        ((P.card : ℝ)*(delta*(J : ℝ)*V0)^2) := exceptional_fraction_average_bound P hP hn Q J M S hS hQ _ hT
    _ ≤ (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(C*(J : ℝ)*V0)/
        ((P.card : ℝ)*(delta*(J : ℝ)*V0)^2) := by
      gcongr
    _ = _ := by field_simp

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_FrozenSieveMean
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseFrozen
open ErdosInverseSpectrum ErdosHyperbolaIdentities

theorem frozenIntegers_card (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) :
    (frozenIntegers N w p q b v a).card = (frozenCoordinates N w p q b v a).card := by
  unfold frozenIntegers
  exact Finset.card_image_of_injective _ Int.ofNat_injective

theorem frozenIntegers_subset (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) :
    frozenIntegers N w p q b v a ⊆ Finset.Ico (0 : ℤ) (N : ℤ) := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hjN := (mem_frozenCoordinates N w p q b v a j).mp hj |>.1
  exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _,by exact_mod_cast hjN⟩

end ErdosInverseFrozen

end

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseSpectrum

theorem frozen_upper (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ),w0 ≤ w → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        ((frozenCoordinates N w p q b v a).card : ℝ) ≤ C*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := SmallSieveUpper.progression_small_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro N w p q b v a hw hN hcop
  exact hupper N w N (b+(q : ℤ)*v) (p*q) a hw hN (by simp) hcop

theorem frozen_exceptional_mean_jb247_oai (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (N Q : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
        (U : Finset ℕ) (delta : ℝ),
        w0 ≤ w → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        (∀ u ∈ U,u.Prime) → (∀ u ∈ U,u ≤ Q) → 0 < U.card → 0 < delta →
        (∑ u ∈ U,((frozenExceptional N w p q b v a u delta (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))/(U.card : ℝ) ≤
          (4+8*Real.pi^2)*C*((N : ℝ)+(Q : ℝ)^2)/
            ((U.card : ℝ)*delta^2*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := frozen_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro N Q w p q b v a U delta hw hN hcop hU hQ hn hd
  have hw2 : 2 ≤ w := hw0.trans hw
  have hwpos : 0 < w := by linarith
  have hNpos : 0 < N := by
    exact_mod_cast (Real.rpow_pos_of_pos hwpos eta).trans_le hN
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr hwpos).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hm : ((frozenIntegers N w p q b v a).card : ℝ) ≤ C*(N : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [frozenIntegers_card]
    exact hupper N w p q b v a hw hN hcop
  exact exceptional_average_of_survivor_upper U hU hn Q N hNpos 0 _
    (by simpa only [zero_add] using frozenIntegers_subset N w p q b v a) hQ
    delta _ C hd hV hm

end ErdosInverseFrozen

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosInverseFrozen.frozen_exceptional_mean_jb247_oai := @OAI.Erdos970.ErdosInverseFrozen.frozen_exceptional_mean_jb247_oai
