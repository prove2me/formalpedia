-- Prove2me | solution 1 for OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:32.786309+00:00
-- url     : https://prove2.me/submissions/0049ad97-e2a7-4951-9ad3-e4f5ad727772

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
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
import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
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
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J008
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_uniform_riesz_contour_bound_jb247

section
-- module Solutions.OAIQ247_JB.Erdos970_Consequences
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Real
open scoped Topology

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using! HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

end Erdos970
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RealCoprimeResidueCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualUnitClasses
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
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

theorem mem_crtNat {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) (hpos : 0 < ∏ i, m i) (k : ℕ) :
    k ∈ crtNat m hcop E ↔ k < ∏ i, m i ∧ ∀ i, (k : ZMod (m i)) ∈ E i := by
  let : NeZero (∏ i, m i) := ⟨hpos.ne'⟩
  constructor
  · intro hk
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
    refine ⟨ZMod.val_lt r, ?_⟩
    have hh : (r.val : ZMod (∏ i, m i)) ∈ ErdosInverseCRT.crtResidues m hcop E := by
      simpa using hr
    have hx := ErdosInverseCRT.intCast_mem_crtResidues m hcop E (r.val : ℤ)
    simp only [Int.cast_natCast] at hx
    exact hx.mp hh
  · rintro ⟨hk,he⟩
    apply Finset.mem_image.mpr
    refine ⟨(k : ZMod (∏ i,m i)), ?_, ZMod.val_natCast_of_lt hk⟩
    have hx := ErdosInverseCRT.intCast_mem_crtResidues m hcop E (k : ℤ)
    simp only [Int.cast_natCast] at hx
    exact hx.mpr he

theorem crtNat_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) (hpos : 0 < ∏ i, m i) :
    (crtNat m hcop E).card = ∏ i, (E i).card := by
  let : NeZero (∏ i, m i) := ⟨hpos.ne'⟩
  rw [crtNat, Finset.card_image_of_injective _ (ZMod.val_injective _),
    ErdosInverseCRT.crtResidues_card]

end ErdosUnitLifts

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonquadraticZeroFree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

lemma modulusHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ modulusHeight q t := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have ht := abs_nonneg t
  have hlt : 1 < Real.log (|t|+6) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans (by linarith))
  unfold modulusHeight
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_RieszMellinKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma rieszWeight_eq_zero {x : ℝ} (hx : 1 ≤ x) : rieszWeight x = 0 :=
  max_eq_right (sub_nonpos.mpr hx)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszIntegrand
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped BigOperators

lemma tsum_riesz_eq_finite (f : ℕ → ℂ) {X : ℝ} (hX : 0 < X) :
    (∑' n:ℕ, f n*(rieszWeight ((n:ℝ)/X):ℂ)) = rieszSum f X := by
  unfold rieszSum
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊X⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hXn : X < (n:ℝ) := (Nat.floor_lt hX.le).mp hn'
  have hw : rieszWeight ((n:ℝ)/X) = 0 := rieszWeight_eq_zero
    ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RecoveryScale
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma rpow_perron_sigma {X : ℝ} (hX : 1 < X) :
    X^(1+(Real.log X)⁻¹) = X*Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < X),mul_add,mul_one,
    mul_inv_cancel₀ (Real.log_pos hX).ne',Real.exp_add,Real.exp_log (by linarith : 0 < X)]

lemma rpow_rieszContourLeft {X : ℝ} (hX : 0 < X) (a : ℝ) (q : ℕ) (T : ℝ) :
    X^(rieszContourLeft a q T) = X*Real.exp (-a*Real.log X/(modulusHeight q T)^2) := by
  rw [Real.rpow_def_of_pos hX]
  have he : Real.log X*rieszContourLeft a q T =
      Real.log X+(-a*Real.log X/(modulusHeight q T)^2) := by unfold rieszContourLeft; ring
  rw [he,Real.exp_add,Real.exp_log hX]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz

lemma rieszWeight_scaled {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    (1+delta)*rieszWeight (u/(1+delta)) = max (1+delta-u) 0 := by
  have hp : 0 < 1+delta := by linarith
  by_cases hu : u ≤ 1+delta
  · have hratio : u/(1+delta) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_left (sub_nonneg.mpr hratio),max_eq_left (sub_nonneg.mpr hu)]
    field_simp
  · have hratio : 1 ≤ u/(1+delta) := (le_div_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_right (sub_nonpos.mpr hratio),
      max_eq_right (show 1+delta-u ≤ 0 by linarith),mul_zero]

lemma rieszDifferenceWeight_eq {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u =
      ((1+delta)*rieszWeight (u/(1+delta))-rieszWeight u)/delta := by
  rw [rieszWeight_scaled hd]
  rfl

lemma rieszDifferenceWeight_nonneg {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    0 ≤ rieszDifferenceWeight delta u := by
  unfold rieszDifferenceWeight
  apply div_nonneg _ hd.le
  exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)

lemma rieszDifferenceWeight_le_one {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u ≤ 1 := by
  have hm : max (1+delta-u) 0 ≤ max (1-u) 0+delta := by
    apply max_le
    · have h := le_max_left (1-u) 0
      linarith
    · have h := le_max_right (1-u) 0
      linarith
  unfold rieszDifferenceWeight
  exact (div_le_iff₀ hd).mpr (by linarith)

lemma rieszDifferenceWeight_eq_one {delta u : ℝ} (hd : 0 < delta) (hu : u ≤ 1) :
    rieszDifferenceWeight delta u = 1 := by
  unfold rieszDifferenceWeight
  rw [max_eq_left (show 0 ≤ 1+delta-u by linarith),max_eq_left (show 0 ≤ 1-u by linarith)]
  have he : 1+delta-u-(1-u) = delta := by ring
  rw [he,div_self hd.ne']

lemma riesz_rescaled_difference {delta X : ℝ} (hd : 0 < delta) (_hX : 0 < X) (n : ℝ) :
    ((1+delta)*rieszWeight (n/((1+delta)*X))-rieszWeight (n/X))/delta =
      rieszDifferenceWeight delta (n/X) := by
  rw [rieszDifferenceWeight_eq hd]
  have he : n/((1+delta)*X) = (n/X)/(1+delta) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]




open scoped BigOperators

lemma rieszSum_extend (f : ℕ → ℂ) {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    rieszSum f X = ∑ n ∈ Finset.range (⌊Y⌋₊+1), f n*(rieszWeight ((n:ℝ)/X):ℂ) := by
  rw [← tsum_riesz_eq_finite f hX]
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊Y⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hYn : Y < (n:ℝ) := (Nat.floor_lt (hX.le.trans hXY)).mp hn'
  have hw := rieszWeight_eq_zero (x := (n:ℝ)/X) ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

lemma rieszRecovery_eq_sum (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta =
      ∑ n ∈ Finset.range (⌊(1+delta)*X⌋₊+1), f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  unfold rieszRecovery
  rw [rieszSum_extend f hX hXY]
  unfold rieszSum
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hw := congrArg Complex.ofReal (riesz_rescaled_difference hd hX (n:ℝ))
  push_cast at hw
  calc
    _ = f n * ((((1+delta:ℝ):ℂ)*(rieszWeight ((n:ℝ)/((1+delta)*X)):ℂ)-
        (rieszWeight ((n:ℝ)/X):ℂ))/(delta:ℂ)) := by ring
    _ = _ := by push_cast; rw [hw]

lemma rieszRecovery_sub_sharp (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta-sharpSum f X =
      ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊(1+delta)*X⌋₊+1),
        f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  have hfloor : ⌊X⌋₊+1 ≤ ⌊(1+delta)*X⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hXY) 1
  have hprefix : (∑ n ∈ Finset.range (⌊X⌋₊+1),
      f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) = sharpSum f X := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ ⌊X⌋₊ := by simp only [Finset.mem_range] at hn; omega
    have hnX : (n:ℝ) ≤ X := (show (n:ℝ) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hn').trans (Nat.floor_le hX.le)
    rw [rieszDifferenceWeight_eq_one hd ((div_le_iff₀ hX).mpr (by linarith)),Complex.ofReal_one,mul_one]
  have hs := Finset.sum_range_add_sum_Ico (fun n:ℕ => f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) hfloor
  rw [hprefix] at hs
  rw [rieszRecovery_eq_sum f hX hd,← hs,add_sub_cancel_left]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem norm_rieszRecovery_sub_sharp (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖rieszRecovery f X delta-sharpSum f X‖ ≤ (delta*X+1)*Real.log ((1+delta)*X) := by
  have hXp : 0 < X := by linarith
  let Y : ℝ := (1+delta)*X
  have hXY : X ≤ Y := by dsimp only [Y] <;> nlinarith [mul_pos hd hXp]
  have hY1 : 1 ≤ Y := hX.trans hXY
  have hYp : 0 < Y := by linarith
  have hfloor : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  let S := Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)
  have hcard : (S.card:ℝ) ≤ delta*X+1 := by
    dsimp only [S]
    rw [Nat.card_Ico,Nat.cast_sub (Nat.add_le_add_right hfloor 1)]
    push_cast
    have hy := Nat.floor_le hYp.le
    have hx := Nat.lt_floor_add_one X
    dsimp only [Y] at hy
    nlinarith
  have hpoint (n:ℕ) (hn : n ∈ S) :
      ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ Real.log Y := by
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hnf : n ≤ ⌊Y⌋₊ := by omega
    have hnY : (n:ℝ) ≤ Y := (show (n:ℝ) ≤ (⌊Y⌋₊:ℝ) by exact_mod_cast hnf).trans (Nat.floor_le hYp.le)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (rieszDifferenceWeight_nonneg hd _)]
    calc
      _ ≤ ‖f n‖ := by
        have h := mul_le_mul_of_nonneg_left (rieszDifferenceWeight_le_one hd ((n:ℝ)/X)) (norm_nonneg (f n))
        simpa only [mul_one] using h
      _ ≤ Real.log (n:ℝ) := hcoeff n hnp
      _ ≤ Real.log Y := Real.log_le_log (by exact_mod_cast hnp) hnY
  rw [rieszRecovery_sub_sharp f hXp hd]
  change ‖∑ n ∈ S, f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ (delta*X+1)*Real.log Y
  calc
    _ ≤ ∑ n ∈ S, ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, Real.log Y := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*Real.log Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hY1)

lemma norm_rieszRecovery_le (f : ℕ → ℂ) (X : ℝ) {delta : ℝ} (hd : 0 < delta) :
    ‖rieszRecovery f X delta‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta := by
  unfold rieszRecovery
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ‖((1+delta:ℝ):ℂ)*rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 1+delta)]

theorem sharpSum_norm_le_riesz (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖sharpSum f X‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta +
        (delta*X+1)*Real.log ((1+delta)*X) := by
  have he := norm_rieszRecovery_sub_sharp f hcoeff hX hd
  have hr := norm_rieszRecovery_le f X hd
  have ht := norm_add_le (sharpSum f X-rieszRecovery f X delta) (rieszRecovery f X delta)
  rw [sub_add_cancel,norm_sub_rev] at ht
  linarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma character_vonMangoldt_norm_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ Real.log (n:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (chi.norm_le_one n)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    _ ≤ _ := ArithmeticFunction.vonMangoldt_le_log

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrincipalPrimePowers
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma principalDifference_norm_le (q : ℕ) [NeZero q] (n : ℕ) :
    ‖principalDifference q n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  unfold principalDifference
  by_cases hu : IsUnit (n:ZMod q)
  · rw [MulChar.one_apply hu,one_mul,sub_self,norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg
  · rw [MulChar.map_nonunit _ hu,zero_mul,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

lemma excluded_primePower_dvd_power (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hLambda : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hu : ¬IsUnit (n:ZMod q)) : n ∣ q^(Nat.log 2 N) := by
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff n).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda)
  have hpq : p ∣ q := by
    by_contra h
    apply hu
    rw [← he,Nat.cast_pow]
    exact ((ZMod.isUnit_prime_iff_not_dvd hp).mpr h).pow k
  have h2 : 2^k ≤ n := by rw [← he]; gcongr; exact hp.two_le
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) (h2.trans hn)
  rw [← he]
  exact (pow_dvd_pow p hkN).trans (pow_dvd_pow_of_dvd hpq _)

lemma principalDifference_eq_zero_of_not_dvd (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hnd : ¬n ∣ q^(Nat.log 2 N)) : principalDifference q n = 0 := by
  by_cases hl : ArithmeticFunction.vonMangoldt n = 0
  · simp only [principalDifference,hl,Complex.ofReal_zero,mul_zero,sub_self]
  · by_cases hu : IsUnit (n:ZMod q)
    · simp only [principalDifference,MulChar.one_apply hu,one_mul,sub_self]
    · exact (hnd (excluded_primePower_dvd_power q hn hl hu)).elim

theorem norm_principal_sharp_difference (q : ℕ) [NeZero q] (X : ℝ) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Nat.log 2 ⌊X⌋₊:ℝ)*Real.log (q:ℝ) := by
  let K : ℕ := Nat.log 2 ⌊X⌋₊
  let N := Finset.range (⌊X⌋₊+1)
  let D := (q^K).divisors
  let S := N ∩ D
  have hqpow : q^K ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hsub : S ⊆ N := Finset.inter_subset_left
  have hsum : (∑ n ∈ S, principalDifference q n) = ∑ n ∈ N, principalDifference q n := by
    apply Finset.sum_subset hsub
    intro n hn hnS
    have hn' : n ≤ ⌊X⌋₊ := by simpa only [N,Finset.mem_range,Nat.lt_add_one_iff] using hn
    apply principalDifference_eq_zero_of_not_dvd q hn'
    intro hd
    apply hnS
    exact Finset.mem_inter.mpr ⟨hn,Nat.mem_divisors.mpr ⟨hd,hqpow⟩⟩
  unfold sharpSum
  rw [← Finset.sum_sub_distrib]
  change ‖∑ n ∈ N, principalDifference q n‖ ≤ (K:ℝ)*Real.log (q:ℝ)
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ S, ‖principalDifference q n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => principalDifference_norm_le q n)
    _ ≤ ∑ n ∈ D, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^K:ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

lemma natLog_floor_le_realLog {X : ℝ} (hX : 1 ≤ X) :
    (Nat.log 2 ⌊X⌋₊:ℝ) ≤ Real.log X/Real.log 2 := by
  have hfloor : ⌊X⌋₊ ≠ 0 := by
    intro hz
    have h := Nat.lt_floor_add_one X
    rw [hz] at h
    norm_num at h
    linarith
  have hNat := Nat.pow_log_le_self 2 hfloor
  have hp : (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ X :=
    (show (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hNat).trans
      (Nat.floor_le (by linarith))
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 ⌊X⌋₊)) hp
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hlog

theorem norm_principal_sharp_difference_real (q : ℕ) [NeZero q] {X : ℝ} (hX : 1 ≤ X) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Real.log X/Real.log 2)*Real.log (q:ℝ) := by
  apply (norm_principal_sharp_difference q X).trans
  exact mul_le_mul_of_nonneg_right (natLog_floor_le_realLog hX)
    (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PrincipalLogPower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma sharpSum_vonMangoldt_eq {X : ℝ} (hX : 0 ≤ X) :
    sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X = (_root_.Erdos970.ChebyshevPsi X:ℂ) := by
  unfold sharpSum _root_.Erdos970.ChebyshevPsi
  rw [Nat.floor_add_one hX,Complex.ofReal_sum]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCountAbel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeCountAbel

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology

lemma mainKernel_continuous {a b : ℝ} (ha : 2 ≤ a) : ContinuousOn mainKernel (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  apply ContinuousAt.continuousWithinAt
  unfold mainKernel
  fun_prop (disch := simp [hlt0])

lemma mainKernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable mainKernel volume a b :=
  (mainKernel_continuous ha).intervalIntegrable_of_Icc hab

end ErdosPrimeInputs.PrimeCountAbel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueSqrtSplit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

lemma residuePsi_character_sum {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X : ℝ) :
    (residuePsi a X:ℂ) = (q.totient:ℂ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X := by
  classical
  unfold residuePsi
  rw [Complex.ofReal_sum]
  simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha]
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  unfold sharpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma residuePsi_error_le {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X E : ℝ)
    (herror : ∀ chi : DirichletCharacter ℂ q,
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ E) :
    ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ ≤ E := by
  classical
  have hai : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a,(ZMod.inv_mul_of_unit a ha).symm⟩
  have hmain : (∑ chi : DirichletCharacter ℂ q,
      chi a⁻¹ * (if chi=1 then (X:ℂ) else 0)) = (X:ℂ) := by
    simp [MulChar.one_apply hai]
  have hsum : (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))) =
      (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X)-(X:ℂ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,hmain]
  have he : (residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ) =
      (q.totient:ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)) := by
    rw [residuePsi_character_sum a ha X,hsum]
    ring
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (chi : DirichletCharacter ℂ q) :
      ‖chi a⁻¹ * (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ E := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right (chi.norm_le_one a⁻¹)
      (norm_nonneg (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)))
    simp only [one_mul] at h
    exact h.trans (herror chi)
  have hnorm : ‖∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ (q.totient:ℝ)*E := by
    calc
      _ ≤ ∑ chi : DirichletCharacter ℂ q, ‖chi a⁻¹ *
          (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
            (if chi=1 then (X:ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _chi : DirichletCharacter ℂ q, E := Finset.sum_le_sum (fun chi _ => hterm chi)
      _ = _ := by simp [hcard]
  rw [he,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (q.totient:ℝ)⁻¹*((q.totient:ℝ)*E) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = E := by rw [← mul_assoc,inv_mul_cancel₀ hphi.ne',one_mul]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

lemma residuePrimeWeight_eq {q : ℕ} (a : ZMod q) (n : ℕ) :
    residuePrimeWeight a n = if n.Prime ∧ (n:ZMod q)=a then Real.log n else 0 := by
  classical
  by_cases hp : n.Prime
  · by_cases ha : (n:ZMod q)=a
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha]
  · simp [residuePrimeWeight,hp]

lemma residuePsi_sub_theta_bounds {q : ℕ} (a : ZMod q) (X : ℝ) :
    0 ≤ residuePsi a X-residueTheta a X ∧
    residuePsi a X-residueTheta a X ≤ Chebyshev.psi X-Chebyshev.theta X := by
  classical
  rw [residuePsi,residueTheta,← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro n _
    unfold residuePrimeWeight
    split_ifs
    · simp only [sub_self,le_refl]
    · simpa only [sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,
      ← Finset.sum_sub_distrib,← Nat.range_succ_eq_Icc_zero]
    apply Finset.sum_le_sum
    intro n _
    unfold residuePrimeWeight
    by_cases hp : n.Prime
    · simp [hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa only [hp,ite_false, if_false,sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_le a n

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology BigOperators

lemma intervalPrimes_zero_eq {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    intervalPrimes 0 X q r = (range (⌊X⌋₊+1)).filter
      (fun n:ℕ => n.Prime ∧ (n:ZMod q)=(r:ZMod q)) := by
  classical
  ext n
  have hm : (n:ZMod q)=(r:ZMod q) ↔ Int.ModEq (q:ℤ) (n:ℤ) r := by
    simpa using (ZMod.intCast_eq_intCast_iff (n:ℤ) r q)
  rw [mem_intervalPrimes,mem_filter,mem_range,hm]
  constructor
  · rintro ⟨hp,_,hn,hr⟩
    refine ⟨Nat.lt_succ_of_le ((Nat.le_floor_iff hX).mpr ?_),hp,hr⟩
    simpa only [zero_add] using hn
  · rintro ⟨hn,hp,hr⟩
    refine ⟨hp,by exact_mod_cast hp.pos,?_,hr⟩
    simpa only [zero_add] using (Nat.le_floor_iff hX).mp (Nat.le_of_lt_succ hn)

lemma intervalPrimes_card_eq_sum_weight {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * residuePrimeWeight (r:ZMod q) n := by
  classical
  rw [intervalPrimes_zero_eq hX,card_eq_sum_ones,Nat.range_succ_eq_Icc_zero,sum_filter]
  push_cast
  apply sum_congr rfl
  intro n _
  rw [residuePrimeWeight_eq]
  by_cases hp : n.Prime ∧ (n:ZMod q)=(r:ZMod q)
  · have hl : Real.log (n:ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hp.1.pos) (by exact_mod_cast hp.1.ne_one)
    simp [hp,hl]
  · simp [hp]

lemma residueTheta_kernel_integrable (q : ℕ) (a : ZMod q) (X : ℝ) :
    IntegrableOn (fun t => residueTheta a t/(t*Real.log t^2)) (Set.Icc 2 X) volume := by
  conv => arg 1; ext; rw [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_one_div,mul_comm]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc ?_
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hl0 : Real.log x ≠ 0 := (Real.log_pos (by linarith [hx.1])).ne'
  have hd : x*Real.log x^2 ≠ 0 := mul_ne_zero hx0 (pow_ne_zero 2 hl0)
  exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem intervalPrimes_card_eq_theta {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      residueTheta (r:ZMod q) X/Real.log X +
        ∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2) := by
  rw [intervalPrimes_card_eq_sum_weight (by linarith) q r]
  rw [sum_mul_eq_sub_integral_mul₁ (residuePrimeWeight (r:ZMod q))
    (f := fun n => (Real.log n)⁻¹) (by simp [residuePrimeWeight])
    (by simp [residuePrimeWeight]),← intervalIntegral.integral_of_le hX]
  · have hi (f : ℝ → ℝ) :
        ∫ u in 2..X, deriv (fun x => (Real.log x)⁻¹) u*f u =
        ∫ u in 2..X, f u * -(u*Real.log u^2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by simp [field]
    rw [hi]
    simp only [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_inv,mul_neg,
      intervalIntegral.integral_neg,sub_neg_eq_add]
    ring
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z ≠ 0 := (Real.log_pos (by linarith [hz.1])).ne'
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z^2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by linarith [hz.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped Topology BigOperators
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral mainKernel)

lemma residueErrorKernel_integrable {q : ℕ} (a : ZMod q) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) : IntervalIntegrable (residueErrorKernel a) volume u v := by
  apply IntervalIntegrable.sub
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
    exact (residueTheta_kernel_integrable q a v).mono_set (Set.Icc_subset_Icc_left hu)
  · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable hu huv).div_const _

lemma residueErrorKernel_eq {q : ℕ} (a : ZMod q) {t : ℝ} (ht : 0 < t) :
    residueErrorKernel a t = (residueTheta a t-t/(q.totient:ℝ))/(t*Real.log t^2) := by
  unfold residueErrorKernel mainKernel
  field_simp

theorem intervalPrimes_error_eq {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ) =
      2/((q.totient:ℝ)*Real.log 2) +
        (residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X +
          ∫ t in 2..X, residueErrorKernel (r:ZMod q) t := by
  have hli := _root_.Erdos970.integral_log_inv 2 X (by norm_num) hX
  have hi : (∫ t in 2..X, residueErrorKernel (r:ZMod q) t) =
      (∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2)) -
        (∫ t in 2..X, mainKernel t)/(q.totient:ℝ) := by
    unfold residueErrorKernel
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_div]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
        (residueTheta_kernel_integrable q _ X)
    · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable (by norm_num) hX).div_const _
  rw [intervalPrimes_card_eq_theta hX,hi]
  unfold logarithmicIntegral mainKernel
  simp only [one_div]
  rw [hli]
  ring

lemma residueTheta_nonneg {q : ℕ} (a : ZMod q) (t : ℝ) : 0 ≤ residueTheta a t := by
  apply Finset.sum_nonneg
  intro n _
  unfold residuePrimeWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · exact le_refl 0

lemma residueTheta_le_theta {q : ℕ} (a : ZMod q) (t : ℝ) :
    residueTheta a t ≤ Chebyshev.theta t := by
  classical
  rw [residueTheta,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_le_sum
  intro n _
  unfold residuePrimeWeight
  by_cases hp : n.Prime
  · simpa only [hp,ite_true, if_true,ArithmeticFunction.vonMangoldt_apply_prime hp] using
      ArithmeticFunction.vonMangoldt.residueClass_le a n
  · simp [hp]

lemma residueErrorKernel_coarse {q : ℕ} [NeZero q] (a : ZMod q) {t : ℝ} (ht : 2 ≤ t) :
    |residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : t/(q.totient:ℝ) ≤ t := div_le_self ht0.le hphi
  have hnum : |residueTheta a t-t/(q.totient:ℝ)| ≤ (Real.log 4+1)*t := by
    calc
      _ ≤ |residueTheta a t|+|t/(q.totient:ℝ)| := abs_sub _ _
      _ = residueTheta a t+t/(q.totient:ℝ) := by rw [abs_of_nonneg (residueTheta_nonneg a t),abs_of_nonneg (by positivity)]
      _ ≤ Real.log 4*t+t := add_le_add ((residueTheta_le_theta a t).trans
        (Chebyshev.theta_le_log4_mul_x ht0.le)) hdiv
      _ = _ := by ring
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0 < t*Real.log t^2)]
  calc
    _ ≤ ((Real.log 4+1)*t)/(t*Real.log t^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.log 4+1)/Real.log t^2 := by field_simp
    _ ≤ _ := by
      have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sq_le_sq₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).le hl.le |>.mpr hlog)

lemma residueErrorKernel_low_integral {q : ℕ} [NeZero q] (a : ZMod q) {Y : ℝ} (hY : 2 ≤ Y) :
    |∫ t in 2..Y, residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2*Y := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=2) (b:=Y)
    (f:=residueErrorKernel a) (C:=(Real.log 4+1)/(Real.log 2)^2) (fun t ht => by
      rw [Set.uIoc_of_le hY] at ht
      simpa only [Real.norm_eq_abs] using residueErrorKernel_coarse a ht.1.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Y-2)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SiegelWalfisz
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma isUnit_intCast_of_isCoprime {q : ℕ} {r : ℤ} (hr : IsCoprime r (q:ℤ)) :
    IsUnit (r:ZMod q) := by
  obtain ⟨u,v,huv⟩ := hr
  have hc : (u:ZMod q)*(r:ZMod q)+(v:ZMod q)*(q:ZMod q)=1 := by
    have h := congrArg (fun z:ℤ => (z:ZMod q)) huv
    push_cast at h
    exact h
  simp only [ZMod.natCast_self,mul_zero,add_zero] at hc
  apply isUnit_of_dvd_one
  exact ⟨(u:ZMod q),by simpa only [mul_comm] using hc.symm⟩

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LargeModulusSiegelWalfisz
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma cubeHeight_pos {X : ℝ} (hX : 1 < X) : 0 < cubeHeight X :=
  Real.rpow_pos_of_pos (Real.log_pos hX) _

lemma cubeHeight_pow_three {X : ℝ} (hX : 1 ≤ X) : (cubeHeight X)^3 = Real.log X := by
  unfold cubeHeight
  rw [← Real.rpow_mul_natCast (Real.log_nonneg hX)]
  norm_num

lemma cubeHeight_mono {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) : cubeHeight X ≤ cubeHeight Y :=
  Real.rpow_le_rpow (Real.log_pos hX).le (Real.log_le_log (by linarith) hXY) (by norm_num)

lemma cubeHeight_tendsto : Tendsto cubeHeight atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp Real.tendsto_log_atTop

lemma eventually_polynomial_le_exp (K : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℝ in atTop, 1 ≤ h ∧ K*h^n ≤ Real.exp (c*h) := by
  have hl : Tendsto (fun h:ℝ => K*h^n*Real.exp (-c*h)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) c hc).const_mul K
  filter_upwards [eventually_ge_atTop (1:ℝ),hl.eventually (gt_mem_nhds zero_lt_one)] with h hh hsmall
  refine ⟨hh,?_⟩
  have hm := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (c*h)).le
  have he : Real.exp (-c*h)*Real.exp (c*h)=1 := by rw [← Real.exp_add,show -c*h+c*h=0 by ring,Real.exp_zero]
  simpa only [mul_assoc,he,mul_one,one_mul] using hm

lemma exponential_height_bound {h : ℝ} (hh : Real.log 7 ≤ h) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp h) : modulusHeight q (Real.exp h) ≤ 3*h := by
  have hh0 : 0 < h := (Real.log_pos (by norm_num : (1:ℝ)<7)).trans_le hh
  have hT : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh0.le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ h := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  have hsum : Real.exp h+6 ≤ 7*Real.exp h := by linarith
  have hl : Real.log (Real.exp h+6) ≤ Real.log 7+h := by
    have he := Real.log_le_log (by positivity : 0 < Real.exp h+6) hsum
    rwa [Real.log_mul (by norm_num : (7:ℝ)≠0) (Real.exp_ne_zero h),Real.log_exp] at he
  unfold modulusHeight
  rw [abs_of_pos (Real.exp_pos h)]
  linarith

lemma exponential_left_saving {a X : ℝ} (ha : 0 < a) (hX : 1 < X)
    (hh : Real.log 7 ≤ cubeHeight X) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp (cubeHeight X)) :
    Real.exp (-a*Real.log X/(modulusHeight q (Real.exp (cubeHeight X)))^2) ≤
      Real.exp (-(a/9)*cubeHeight X) := by
  let h := cubeHeight X
  let H := modulusHeight q (Real.exp h)
  have hh0 : 0 < h := cubeHeight_pos hX
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh q hq
  have hsq : H^2 ≤ 9*h^2 := by nlinarith [sq_nonneg (3*h-H)]
  have hcube : h^3 = Real.log X := cubeHeight_pow_three hX.le
  apply Real.exp_le_exp.mpr
  change -a*Real.log X/H^2 ≤ -(a/9)*h
  apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
  rw [← hcube]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (a/9)*h by positivity)
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_exponential_contour_savings {a : ℝ} (ha : 0 < a) (ha100 : a ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      let T := Real.exp (cubeHeight X)
      let H := modulusHeight q T
      H^3*Real.exp (-a*Real.log X/H^2) ≤ Real.exp (-c*cubeHeight X) ∧
      H^3/(1+T^2) ≤ Real.exp (-c*cubeHeight X) ∧
      Real.log X/T ≤ Real.exp (-c*cubeHeight X) := by
  let c : ℝ := a/18
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hc2 : c ≤ 1/2 := by dsimp [c] <;> linarith
  refine ⟨c,hc,hc2,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (Real.log 7)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 27 3 hc)] with X hX hh7 hhpoly
  have hx1 : 1 < X := by linarith
  have hx0 : 0 < X := by linarith
  have hL : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  refine ⟨hX,hL,?_⟩
  intro q _ hq
  let h := cubeHeight X
  let T := Real.exp h
  let H := modulusHeight q T
  have hh : 0 < h := cubeHeight_pos hx1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh7 q hq
  have hHp : H^3 ≤ Real.exp (c*h) := by
    have hp := pow_le_pow_left₀ hH.le hHle 3
    calc
      _ ≤ (3*h)^3 := hp
      _ = 27*h^3 := by ring
      _ ≤ _ := hhpoly.2
  have hLp : Real.log X ≤ Real.exp (c*h) := by
    calc
      _ = h^3 := (cubeHeight_pow_three hx1.le).symm
      _ ≤ 27*h^3 := by nlinarith [pow_nonneg hh.le 3]
      _ ≤ _ := hhpoly.2
  have hs := exponential_left_saving ha hx1 hh7 q hq
  have hT2 : T^2 = Real.exp (2*h) := by
    dsimp [T]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ Real.exp (c*h)*Real.exp (-(a/9)*h) :=
        mul_le_mul hHp hs (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-c*h) := by rw [← Real.exp_add]; congr 1; dsimp [c] <;> ring
  · calc
      _ ≤ H^3/T^2 := div_le_div_of_nonneg_left (by positivity) (by dsimp [T] <;> positivity) (by linarith)
      _ ≤ Real.exp (c*h)/T^2 := div_le_div_of_nonneg_right hHp (sq_nonneg _)
      _ = Real.exp (c*h-2*h) := by rw [hT2,Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)
  · calc
      _ ≤ Real.exp (c*h)/T := div_le_div_of_nonneg_right hLp (by dsimp [T] <;> positivity)
      _ = Real.exp (c*h-h) := by dsimp [T]; rw [Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem riesz_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨a,ha,ha100,C,hC,B,hB,hcontour⟩ := exists_uniform_riesz_contour_bound_jb247
  obtain ⟨c,hc,hc2,hsavings⟩ := eventually_exponential_contour_savings ha ha100
  let P : ℝ := 4*Real.pi*C+16*C*Real.exp 1+8*(B+1)*Real.exp 1
  let K : ℝ := (1/(2*Real.pi))*P
  have hP : 0 < P := by dsimp only [P] <;> positivity
  have hK : 0 < K := by dsimp only [K] <;> positivity
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hsavings] with X hX
  intro q _ chi hchi hq
  obtain ⟨hX3,hL1,hSavings⟩ := hX
  obtain ⟨hleft,hhor,hratio⟩ := hSavings q hq
  let L : ℝ := Real.log X
  let T : ℝ := Real.exp (cubeHeight X)
  let R : ℝ := Real.exp (-c*cubeHeight X)
  let H : ℝ := modulusHeight q T
  let sigma : ℝ := 1+L⁻¹
  have hXp : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := Real.exp_pos _
  have hs1 : 1 < sigma := by
    have hi : 0 < L⁻¹ := inv_pos.mpr hLp
    dsimp only [sigma]
    linarith
  have hs2 : sigma ≤ 2 := by
    have hinv : L⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hLp).mpr (by linarith)
    dsimp only [sigma]
    linarith
  have h := hcontour q chi hchi X sigma T (by linarith) hs1 hs2 hTp
  have hrightpow : X^sigma = X*Real.exp 1 := rpow_perron_sigma hX1
  have hleftpow : X^(rieszContourLeft a q T) = X*Real.exp (-a*L/H^2) := rpow_rieszContourLeft hXp a q T
  have hinv : (sigma-1)⁻¹ = L := by dsimp only [sigma]; rw [add_sub_cancel_left,inv_inv]
  rw [hrightpow,hleftpow,hinv] at h
  change H^3*Real.exp (-a*L/H^2) ≤ R at hleft
  change H^3/(1+T^2) ≤ R at hhor
  change L/T ≤ R at hratio
  have hBL := mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) hB
  have hLB : L+B ≤ (B+1)*L := by nlinarith only [hBL]
  have htail : (L+B)/T ≤ (B+1)*R := by
    calc
      _ ≤ ((B+1)*L)/T := div_le_div_of_nonneg_right hLB hTp.le
      _ = (B+1)*(L/T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 4*Real.pi*C*X by positivity)
  have h2 := mul_le_mul_of_nonneg_left hhor (show 0 ≤ 16*C*Real.exp 1*X by positivity)
  have h3 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 8*Real.exp 1*X by positivity)
  have he : 4*Real.pi*C*H^3*(X*Real.exp (-a*L/H^2)) +
      16*C*H^3*(X*Real.exp 1)/(1+T^2)+8*(L+B)*(X*Real.exp 1)/T ≤ P*X*R := by
    calc
      _ = (4*Real.pi*C*X)*(H^3*Real.exp (-a*L/H^2)) +
          (16*C*Real.exp 1*X)*(H^3/(1+T^2))+(8*Real.exp 1*X)*((L+B)/T) := by ring
      _ ≤ (4*Real.pi*C*X)*R+(16*C*Real.exp 1*X)*R+
          (8*Real.exp 1*X)*((B+1)*R) := add_le_add (add_le_add h1 h2) h3
      _ = _ := by dsimp only [P] <;> ring
  apply h.trans
  calc
    _ ≤ (1/(2*Real.pi))*(P*X*R) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = K*X*Real.exp (-c*cubeHeight X) := by dsimp only [K,R] <;> ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma cubeHeight_le_log {X : ℝ} (hX : 1 ≤ X) (hh : 1 ≤ cubeHeight X) :
    cubeHeight X ≤ Real.log X := by
  have hp : 1 ≤ (cubeHeight X)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ cubeHeight X by linarith)
  rw [← cubeHeight_pow_three hX]
  nlinarith

lemma exponential_recovery_scale {d X : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X) :
    let delta := Real.exp (-d*cubeHeight X)
    let Y := (1+delta)*X
    0 < delta ∧ delta ≤ 1 ∧ 1 ≤ delta*X ∧ X ≤ Y ∧ Y ≤ 2*X ∧
      cubeHeight X ≤ cubeHeight Y ∧ Real.log Y ≤ 2*Real.log X := by
  let delta := Real.exp (-d*cubeHeight X)
  let Y := (1+delta)*X
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < cubeHeight X := cubeHeight_pos hx1
  have hdpos : 0 < delta := Real.exp_pos _
  have hdle : delta ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsmall : d*cubeHeight X ≤ Real.log X := by
    calc
      _ ≤ cubeHeight X := by nlinarith
      _ ≤ _ := cubeHeight_le_log hx1.le hh
  have hpower : Real.exp (d*cubeHeight X) ≤ X := by
    simpa only [Real.exp_log hx0] using Real.exp_le_exp.mpr hsmall
  have hid : delta*Real.exp (d*cubeHeight X)=1 := by
    dsimp [delta]
    rw [← Real.exp_add,show -d*cubeHeight X+d*cubeHeight X=0 by ring,Real.exp_zero]
  have hdX : 1 ≤ delta*X := by
    have hm := mul_le_mul_of_nonneg_left hpower hdpos.le
    rwa [hid] at hm
  have hXY : X ≤ Y := by dsimp [Y] <;> nlinarith
  have hY2 : Y ≤ 2*X := by dsimp [Y] <;> nlinarith
  have hY0 : 0 < Y := hx0.trans_le hXY
  have hhY : cubeHeight X ≤ cubeHeight Y := cubeHeight_mono hx1 hXY
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hlogY : Real.log Y ≤ 2*Real.log X := by
    have h := Real.log_le_log hY0 hY2
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne'] at h
    linarith
  exact ⟨hdpos,hdle,hdX,hXY,hY2,hhY,hlogY⟩

lemma exponential_recovery_tail {c X : ℝ} (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X)
    (hpoly : (cubeHeight X)^3 ≤ Real.exp ((c/4)*cubeHeight X)) :
    let delta := Real.exp (-(c/2)*cubeHeight X)
    (delta*X+1)*Real.log ((1+delta)*X) ≤ 4*X*Real.exp (-(c/4)*cubeHeight X) := by
  let delta := Real.exp (-(c/2)*cubeHeight X)
  obtain ⟨hd,_,hdX,hXY,_,_,hlogY⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hh
  have hx0 : 0 < X := by linarith
  have hY0 : 0 < (1+delta)*X := by positivity
  have hlogY0 : 0 ≤ Real.log ((1+delta)*X) := Real.log_nonneg (by linarith)
  have hprod : delta*Real.log X ≤ Real.exp (-(c/4)*cubeHeight X) := by
    calc
      _ = delta*(cubeHeight X)^3 := by rw [cubeHeight_pow_three (by linarith : 1≤X)]
      _ ≤ delta*Real.exp ((c/4)*cubeHeight X) := mul_le_mul_of_nonneg_left hpoly hd.le
      _ = _ := by dsimp [delta]; rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (2*delta*X)*(2*Real.log X) := mul_le_mul (by nlinarith) hlogY hlogY0 (by positivity)
    _ = 4*X*(delta*Real.log X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem sharp_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,C,hc,hc2,hC,hRiesz⟩ := riesz_character_exponential
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hRiesz
  refine ⟨c/4,5*C+4,by positivity,by linarith,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop X0,eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 1 3 (by positivity : 0 < c/4))]
    with X hthreshold hX hpoly
  intro q _ chi hchi hq
  let h := cubeHeight X
  let delta := Real.exp (-(c/2)*h)
  let Y := (1+delta)*X
  let f : ℕ → ℂ := fun n => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < h := cubeHeight_pos hx1
  obtain ⟨hd,hd1,hdX,hXY,hY2,hhY,_⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hpoly.1
  have hqY : (q:ℝ) ≤ Real.exp (cubeHeight Y) := hq.trans (Real.exp_le_exp.mpr hhY)
  have hx := hX0 X hthreshold q chi hchi hq
  have hy := hX0 Y (hthreshold.trans hXY) q chi hchi hqY
  have hdecay : Real.exp (-c*cubeHeight Y) ≤ Real.exp (-c*h) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hy' : ‖rieszSum f Y‖ ≤ 2*C*X*Real.exp (-c*h) := by
    calc
      _ ≤ C*Y*Real.exp (-c*cubeHeight Y) := hy
      _ ≤ C*Y*Real.exp (-c*h) := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ C*(2*X)*Real.exp (-c*h) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hY2 hC.le) (Real.exp_pos _).le
      _ = _ := by ring
  have hnum : (1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖ ≤ 5*C*X*Real.exp (-c*h) := by
    have h1 := mul_le_mul_of_nonneg_left hy' (show 0 ≤ 1+delta by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show 1+delta ≤ 2 by linarith)
      (show 0 ≤ 2*C*X*Real.exp (-c*h) by positivity)
    apply (add_le_add (h1.trans h2) hx).trans_eq
    ring
  have hterm : ((1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖)/delta ≤
      5*C*X*Real.exp (-(c/4)*h) := by
    calc
      _ ≤ (5*C*X*Real.exp (-c*h))/delta := div_le_div_of_nonneg_right hnum hd.le
      _ = 5*C*X*Real.exp (-(c/2)*h) := by
        dsimp [delta]
        rw [mul_div_assoc,← Real.exp_sub]
        congr 1
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have htail := exponential_recovery_tail hc hc2 hX hpoly.1 (by simpa only [one_mul] using hpoly.2)
  have hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ) :=
    fun n _ => character_vonMangoldt_norm_le chi n
  have hsharp := sharpSum_norm_le_riesz f hcoeff (show 1 ≤ X by linarith) hd
  apply (hsharp.trans (add_le_add hterm htail)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_polynomial_le_X_exp (K : ℝ) (n : ℕ) (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, K*(cubeHeight X)^n ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (d+1)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp K n (by norm_num : (0:ℝ)<1))]
    with X hX hd hp
  let h := cubeHeight X
  have hh : 0 ≤ h := by linarith [hp.1]
  have hh2 : h ≤ h^2 := by nlinarith [hp.1]
  have hsq : d+1 ≤ h^2 := hd.trans hh2
  have hm := mul_le_mul_of_nonneg_right hsq hh
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : h ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  calc
    _ ≤ Real.exp h := by simpa only [one_mul] using hp.2
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_sqrt_le_X_exp (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 (2*d)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hhd : 2*d ≤ h := (le_max_right _ _).trans hh
  have hsq : 2*d ≤ h^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ h by linarith)
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : Real.log X*((1:ℝ)/2) ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by linarith : 0<X)]
  calc
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_exp_sqrt_log_le {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop,
      Real.exp (-a*Real.sqrt (Real.log X)) ≤ Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 ((d/a)^2)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hh0 : 0 ≤ h := by linarith
  have hsq : (d/a)^2 ≤ h := (le_max_right _ _).trans hh
  have hda : d/a ≤ Real.sqrt h := (Real.le_sqrt (by positivity) hh0).mpr hsq
  have hmul : d ≤ a*Real.sqrt h := by
    have he := (div_le_iff₀ ha).mp hda
    simpa only [mul_comm] using he
  have hsqrt : Real.sqrt (Real.log X) = h*Real.sqrt h := by
    rw [← cubeHeight_pow_three (by linarith : 1≤X),show (cubeHeight X)^3=(cubeHeight X)^2*cubeHeight X by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hh0]
  have hm := mul_le_mul_of_nonneg_right hmul hh0
  apply Real.exp_le_exp.mpr
  rw [hsqrt]
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma ordinary_psi_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ‖sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨a,ha,hPNT⟩ := _root_.Erdos970.Strong_PNT
  obtain ⟨K,hK,hbound⟩ := hPNT.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound.bound,eventually_exp_sqrt_log_le ha hd,
    eventually_ge_atTop (3:ℝ)] with X hb he hX
  have hx0 : 0 < X := by linarith
  change ‖_root_.Erdos970.ChebyshevPsi X-X‖ ≤ K*‖X*Real.exp (-a*(Real.log X)^(1/2:ℝ))‖ at hb
  rw [sharpSum_vonMangoldt_eq hx0.le,← Complex.ofReal_sub,Complex.norm_real]
  simp only [Real.norm_eq_abs] at hb ⊢
  rw [abs_of_nonneg (by positivity : 0≤X*Real.exp (-a*(Real.log X)^(1/2:ℝ))),
    ← Real.sqrt_eq_rpow] at hb
  calc
    _ ≤ K*(X*Real.exp (-a*Real.sqrt (Real.log X))) := hb
    _ ≤ K*(X*Real.exp (-d*cubeHeight X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx0.le) hK.le
    _ = _ := by ring

lemma principal_difference_exponential (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),eventually_polynomial_le_X_exp (1/Real.log 2) 4 d]
    with X hX hpoly
  intro q _ hq
  have hx1 : 1 < X := by linarith
  have hL : 0 ≤ Real.log X := (Real.log_pos hx1).le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ cubeHeight X := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  calc
    _ ≤ (Real.log X/Real.log 2)*Real.log (q:ℝ) := norm_principal_sharp_difference_real q hx1.le
    _ ≤ (Real.log X/Real.log 2)*cubeHeight X := mul_le_mul_of_nonneg_left hql (by positivity)
    _ = (1/Real.log 2)*(cubeHeight X)^4 := by rw [← cubeHeight_pow_three hx1.le]; ring
    _ ≤ _ := hpoly

theorem principal_character_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨K,hK,hOrd⟩ := ordinary_psi_exponential hd
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [principal_difference_exponential d,hOrd] with X hDiff hOrd
  intro q _ hq
  have hn := norm_add_le
    (sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X)
    (sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ))
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add (hDiff q hq) hOrd)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem all_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ K*X*Real.exp (-c*cubeHeight X) := by
  classical
  obtain ⟨c,C,hc,hc2,hC,hNon⟩ := sharp_character_exponential
  obtain ⟨D,hD,hPrin⟩ := principal_character_exponential hc
  refine ⟨c,C+D,hc,hc2,by positivity,?_⟩
  filter_upwards [hNon,hPrin,eventually_ge_atTop (3:ℝ)] with X hNon hPrin hX
  intro q _ chi hq
  have hx0 : 0 ≤ X := by linarith
  have hcb : C*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  have hdb : D*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  by_cases hchi : chi=1
  · subst chi
    simpa using! (hPrin q hq).trans hdb
  · simpa [hchi] using! (hNon q chi hchi hq).trans hcb

theorem residuePsi_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residuePsi a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hall⟩ := all_character_exponential
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hall] with X hX
  intro q _ a ha hq
  have h := residuePsi_error_le a ha X (K*X*Real.exp (-c*cubeHeight X)) (fun chi => hX q chi hq)
  have he : ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ =
      |residuePsi a X-X/(q.totient:ℝ)| := by
    rw [show (q.totient:ℂ) = ((q.totient:ℝ):ℂ) by simp,
      ← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rwa [he] at h

theorem residueTheta_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residueTheta a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hpsi⟩ := residuePsi_exponential
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c,K+C,hc,hc2,by positivity,?_⟩
  filter_upwards [hpsi,eventually_sqrt_le_X_exp c] with X hX hsqrt
  intro q _ a ha hq
  have hgap := residuePsi_sub_theta_bounds a X
  have hb : residuePsi a X-residueTheta a X ≤ C*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := hgap.2.trans (hD X)
      _ ≤ C*Real.sqrt X := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ C*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hsqrt hC.le
      _ = _ := by ring
  calc
    _ ≤ |residuePsi a X-X/(q.totient:ℝ)|+|residuePsi a X-residueTheta a X| := by
      have h := abs_sub_le (residueTheta a X) (residuePsi a X) (X/(q.totient:ℝ))
      rw [abs_sub_comm (residueTheta a X) (residuePsi a X),add_comm] at h
      exact h
    _ ≤ K*X*Real.exp (-c*cubeHeight X)+C*X*Real.exp (-c*cubeHeight X) := by
      rw [abs_of_nonneg hgap.1]
      exact add_le_add (hX q a ha hq) hb
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology

lemma cubeHeight_above_sqrt {X t : ℝ} (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) :
    cubeHeight X/2 ≤ cubeHeight t := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hx1 : 1 < X := by nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : 1 < t := by linarith
  have hhX : 0 < cubeHeight X := cubeHeight_pos hx1
  have hht : 0 < cubeHeight t := cubeHeight_pos ht1
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have he := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0.le] at he
    linarith
  apply (pow_le_pow_iff_left₀ (show 0 ≤ cubeHeight X/2 by positivity) hht.le (by decide : (3:ℕ)≠0)).mp
  rw [show (cubeHeight X/2)^3=(cubeHeight X)^3/8 by ring,
    cubeHeight_pow_three hx1.le,cubeHeight_pow_three ht1.le]
  have hlog := Real.log_pos hx1
  linarith

lemma modulus_exponential_above_sqrt {c X t : ℝ} (hc : c ≤ 1/2)
    (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) {q : ℕ}
    (hq : (q:ℝ) ≤ Real.exp (c*cubeHeight X)) :
    (q:ℝ) ≤ Real.exp (cubeHeight t) := by
  have hx0 : 0 < X := Real.sqrt_pos.mp (by linarith)
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by nlinarith [Real.sq_sqrt hx0.le])
  apply hq.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ cubeHeight X/2 := by nlinarith
    _ ≤ _ := cubeHeight_above_sqrt hX ht

lemma residueErrorKernel_exp_upper {q : ℕ} (a : ZMod q) {K d X t : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t)
    (herror : |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |residueErrorKernel a t| ≤ K*Real.exp (-(d/2)*cubeHeight X) := by
  have ht3 : 3 ≤ t := hX.trans ht
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht3)).le
  have hcompare := cubeHeight_above_sqrt hX ht
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0<t*Real.log t^2)]
  calc
    _ ≤ (K*t*Real.exp (-d*cubeHeight t))/(t*Real.log t^2) :=
      div_le_div_of_nonneg_right herror (by positivity)
    _ = (K*Real.exp (-d*cubeHeight t))/(Real.log t)^2 := by field_simp
    _ ≤ K*Real.exp (-d*cubeHeight t) := div_le_self (by positivity) (by nlinarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK

lemma residueErrorKernel_exp_high_integral {q : ℕ} (a : ZMod q) {K d X : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X)
    (herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |∫ t in Real.sqrt X..X, residueErrorKernel a t| ≤
      K*X*Real.exp (-(d/2)*cubeHeight X) := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=Real.sqrt X) (b:=X)
    (f:=residueErrorKernel a) (C:=K*Real.exp (-(d/2)*cubeHeight X)) (fun t ht => by
      rw [Set.uIoc_of_le hsX] at ht
      simpa only [Real.norm_eq_abs] using
        residueErrorKernel_exp_upper a hK hd hX ht.1.le (herror t ht.1.le))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsX)] at he
  calc
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*(X-Real.sqrt X) := he
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*X :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma large_modulus_siegel_walfisz_eventually :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (r : ℤ), IsUnit (r:ZMod q) →
      (q:ℝ) ≤ Real.exp (c*cubeHeight X) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨d,K,hd,hd2,hK,hθ⟩ := residueTheta_exponential
  obtain ⟨b,hb⟩ := eventually_atTop.mp hθ
  let c : ℝ := d/2
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hc2 : c ≤ 1/2 := by dsimp [c] <;> linarith
  let D : ℝ := (Real.log 4+1)/(Real.log 2)^2
  let E : ℝ := 2/Real.log 2
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨c,E+2*K+D,hc,hc2,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max 3 b)),
    eventually_ge_atTop (3:ℝ),eventually_sqrt_le_X_exp c,
    eventually_polynomial_le_X_exp 1 0 c] with X hs hX hroot hscale
  intro q _ r hr hq
  have hs3 : 3 ≤ Real.sqrt X := (le_max_left _ _).trans hs
  have hsb : b ≤ Real.sqrt X := (le_max_right _ _).trans hs
  have hx0 : 0 < X := by linarith
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by linarith)
  have hL1 : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  have hL : 0 < Real.log X := by linarith
  have hscale1 : 1 ≤ X*Real.exp (-c*cubeHeight X) := by simpa only [pow_zero,mul_one] using hscale
  have herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta (r:ZMod q) t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t) := by
    intro t ht
    exact hb t (hsb.trans ht) q (r:ZMod q) hr
      (modulus_exponential_above_sqrt hc2 hs3 ht hq)
  have hdecay : Real.exp (-d*cubeHeight X) ≤ Real.exp (-c*cubeHeight X) :=
    Real.exp_le_exp.mpr (by dsimp [c] <;> nlinarith)
  have hend : |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X| ≤
      K*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_div,abs_of_pos hL]
    calc
      _ ≤ (K*X*Real.exp (-d*cubeHeight X))/Real.log X :=
        div_le_div_of_nonneg_right (herror X hsX) hL.le
      _ ≤ K*X*Real.exp (-d*cubeHeight X) := div_le_self (by positivity) hL1
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hlo : |∫ t in 2..Real.sqrt X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := residueErrorKernel_low_integral _ (by linarith)
      _ ≤ D*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hroot hD.le
      _ = _ := by ring
  have hhi := residueErrorKernel_exp_high_integral (r:ZMod q) hK.le hd hs3 herror
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (residueErrorKernel_integrable (r:ZMod q) (by norm_num) (by linarith : (2:ℝ)≤Real.sqrt X))
    (residueErrorKernel_integrable (r:ZMod q) (by linarith : (2:ℝ)≤Real.sqrt X) hsX)
  have hint : |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X) := by
    rw [← hsplit]
    exact (abs_add_le _ _).trans (add_le_add hlo hhi)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hconst : |2/((q.totient:ℝ)*Real.log 2)| ≤ E*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = E/(q.totient:ℝ) := by dsimp [E] <;> ring
      _ ≤ E := div_le_self hE.le hphi
      _ ≤ E*(X*Real.exp (-c*cubeHeight X)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale1 hE.le
      _ = _ := by ring
  rw [intervalPrimes_error_eq (by linarith) q r]
  calc
    _ ≤ |2/((q.totient:ℝ)*Real.log 2)|+
        |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X|+
        |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)+
        (D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)) :=
      add_le_add (add_le_add hconst hend) hint
    _ = _ := by ring

theorem large_modulus_siegel_walfisz :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (r : ℤ), 0 < q → IsCoprime r (q:ℤ) →
      (q:ℝ) ≤ Real.exp (c*(Real.log X)^((1:ℝ)/3)) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*(Real.log X)^((1:ℝ)/3)) := by
  obtain ⟨c,C,hc,_hc2,hC,h⟩ := large_modulus_siegel_walfisz_eventually
  obtain ⟨b,hb⟩ := eventually_atTop.mp h
  refine ⟨c,C,max 3 b,hc,hC,le_max_left _ _,?_⟩
  intro X hX q r hq hr hbound
  let _ : NeZero q := ⟨hq.ne'⟩
  exact hb X ((le_max_right _ _).trans hX) q r (isUnit_intCast_of_isCoprime hr) hbound

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeIntervalFlags
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma intervalPrimes_eq_sdiff {u v : ℝ} (hu : 0 ≤ u) (q : ℕ) (r : ℤ) :
    intervalPrimes u (v-u) q r = intervalPrimes 0 v q r \ intervalPrimes 0 u q r := by
  ext p
  simp only [mem_sdiff,mem_intervalPrimes,zero_add,add_sub_cancel]
  constructor
  · rintro ⟨hp,hlo,hhi,hm⟩
    refine ⟨⟨hp,by linarith,hhi,hm⟩,?_⟩
    rintro ⟨_,_,hpu,_⟩
    linarith
  · rintro ⟨⟨hp,h0,hhi,hm⟩,hnot⟩
    refine ⟨hp,?_,hhi,hm⟩
    by_contra h
    exact hnot ⟨hp,h0,le_of_not_gt h,hm⟩

lemma intervalPrimes_count_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (q : ℕ) (r : ℤ) :
    ((intervalPrimes u (v-u) q r).card:ℝ) =
      ((intervalPrimes 0 v q r).card:ℝ)-((intervalPrimes 0 u q r).card:ℝ) := by
  have hs : intervalPrimes 0 u q r ⊆ intervalPrimes 0 v q r := by
    intro p hp
    obtain ⟨hpr,h0,hpu,hm⟩ := (mem_intervalPrimes _ _ _ _ _).mp hp
    exact (mem_intervalPrimes _ _ _ _ _).mpr ⟨hpr,h0,by linarith,hm⟩
  rw [intervalPrimes_eq_sdiff hu,card_sdiff_of_subset hs,Nat.cast_sub (card_le_card hs)]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagCutoffSeparation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve
open Erdos970Dependency.SiegelWalfisz
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

theorem interval_AP_li_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ q : ℕ,∀ r : ℤ,
      0 < q → IsCoprime r (q:ℤ) → (q:ℝ) ≤ Real.exp (c*cubeHeight R) →
      |((intervalPrimes R V q r).card:ℝ)-
        (logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ)| ≤
          C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := large_modulus_siegel_walfisz
  refine ⟨c,3*C,X₀,hc,by positivity,hX₀,?_⟩
  intro R V hR hV hVR q r hq hr hmod
  have hR3 : 3 ≤ R := hX₀.trans hR
  have hR0 : 0 ≤ R := by linarith
  have hRV : R ≤ R+V := by linarith
  have hh : cubeHeight R ≤ cubeHeight (R+V) := cubeHeight_mono (by linarith) hRV
  have hmod' : (q:ℝ) ≤ Real.exp (c*cubeHeight (R+V)) :=
    hmod.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hc.le))
  have hlo := hAP R hR q r hq hr hmod
  have hhi := hAP (R+V) (hR.trans hRV) q r hq hr hmod'
  have he : Real.exp (-c*cubeHeight (R+V)) ≤ Real.exp (-c*cubeHeight R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hh (by linarith))
  have hb : C*(R+V)*Real.exp (-c*cubeHeight (R+V)) ≤ 2*C*R*Real.exp (-c*cubeHeight R) := by
    calc
      _ ≤ C*(R+V)*Real.exp (-c*cubeHeight R) := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := by
        have hx := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (show R+V ≤ 2*R by linarith) hC.le)
          (Real.exp_pos (-c*cubeHeight R)).le
        simpa only [mul_assoc,mul_left_comm,mul_comm] using hx
  have hcount : ((intervalPrimes R V q r).card:ℝ)=
      ((intervalPrimes 0 (R+V) q r).card:ℝ)-((intervalPrimes 0 R q r).card:ℝ) := by
    simpa only [add_sub_cancel_left] using intervalPrimes_count_sub hR0 hRV q r
  have hid : ((intervalPrimes R V q r).card:ℝ)-
      (logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ)=
      (((intervalPrimes 0 (R+V) q r).card:ℝ)-logarithmicIntegral (R+V)/(q.totient:ℝ))-
      (((intervalPrimes 0 R q r).card:ℝ)-logarithmicIntegral R/(q.totient:ℝ)) := by
    rw [hcount]
    ring
  rw [hid]
  have ht := abs_add_le
    (((intervalPrimes 0 (R+V) q r).card:ℝ)-logarithmicIntegral (R+V)/(q.totient:ℝ))
    (-(((intervalPrimes 0 R q r).card:ℝ)-logarithmicIntegral R/(q.totient:ℝ)))
  simp only [abs_neg,← sub_eq_add_neg] at ht
  have hs := ht.trans (add_le_add (hhi.trans hb) hlo)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [cubeHeight]
  ring

theorem interval_AP_count_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ q : ℕ,∀ r : ℤ,
      0 < q → IsCoprime r (q:ℤ) → (q:ℝ) ≤ Real.exp (c*cubeHeight R) →
      |((intervalPrimes R V q r).card:ℝ)-
        ((intervalPrimes R V 1 0).card:ℝ)/(q.totient:ℝ)| ≤
          C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_li_error
  refine ⟨c,2*C,X₀,hc,by positivity,hX₀,?_⟩
  intro R V hR hV hVR q r hq hr hmod
  have hR3 : 3 ≤ R := hX₀.trans hR
  have hh : 0 < cubeHeight R := cubeHeight_pos (by linarith)
  have hmod1 : ((1:ℕ):ℝ) ≤ Real.exp (c*cubeHeight R) := by
    simpa using Real.one_le_exp_iff.mpr (mul_nonneg hc.le hh.le)
  have h1 := hAP R V hR hV hVR 1 0 (by norm_num) (by norm_num) hmod1
  have h := hAP R V hR hV hVR q r hq hr hmod
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  simp only [Nat.totient_one,Nat.cast_one,div_one] at h1
  have hp0 : 0 < (q.totient:ℝ) := by linarith
  have hd : |(logarithmicIntegral (R+V)-logarithmicIntegral R-
      ((intervalPrimes R V 1 0).card:ℝ))/(q.totient:ℝ)| ≤ C*R*Real.exp (-c*cubeHeight R) := by
    rw [abs_div,abs_of_pos hp0,abs_sub_comm]
    exact (div_le_div_of_nonneg_right h1 hp0.le).trans (div_le_self (by positivity) hphi)
  have hid : ((intervalPrimes R V q r).card:ℝ)-((intervalPrimes R V 1 0).card:ℝ)/(q.totient:ℝ)=
      (((intervalPrimes R V q r).card:ℝ)-(logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ))+
      (logarithmicIntegral (R+V)-logarithmicIntegral R-((intervalPrimes R V 1 0).card:ℝ))/(q.totient:ℝ) := by ring
  rw [hid]
  have hs := (abs_add_le _ _).trans (add_le_add h hd)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [cubeHeight]
  ring

end ErdosStoppedTagSieve



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_TagCRTPeriodicity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
attribute [local instance] Classical.decEq

lemma intersection_moduli_product (Q : ℕ) (T : Finset ℕ) :
    (∏ i,intersectionModuli Q T i)=Q*(∏ t∈T,t) := by
  rw [Fintype.prod_option]
  simp only [intersectionModuli]
  congr 1
  exact Finset.prod_coe_sort T (fun t : ℕ => t)

lemma baseClasses_card (Q : ℕ) (A : Finset ℕ) (hA : ∀ a∈A,a<Q) :
    (baseClasses Q A).card=A.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  have hh := (ZMod.natCast_eq_natCast_iff' a b Q).mp he
  simpa only [Nat.mod_eq_of_lt (hA a ha),Nat.mod_eq_of_lt (hA b hb)] using hh

lemma mem_baseClasses (Q : ℕ) (A : Finset ℕ) (hA : ∀ a∈A,a<Q) (p : ℕ) :
    (p:ZMod Q)∈baseClasses Q A ↔ p%Q∈A := by
  constructor
  · rintro h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    have hh := (ZMod.natCast_eq_natCast_iff' a p Q).mp he
    rw [Nat.mod_eq_of_lt (hA a ha)] at hh
    exact hh ▸ ha
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨p%Q,hp,?_⟩
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    exact Nat.mod_mod p Q

lemma intersection_moduli_pos (Q : ℕ) (hQ : 0 < Q) (T : Finset ℕ) (hT : ∀ t∈T,t.Prime) :
    0 < ∏ i,intersectionModuli Q T i := by
  rw [intersection_moduli_product]
  exact Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))

theorem mem_intersectionResidues (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (p : ℕ) :
    p∈intersectionResidues Q T A rho hT hQT ↔
      p<Q*(∏ t∈T,t) ∧ p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t := by
  rw [intersectionResidues,ErdosUnitLifts.mem_crtNat _ _ _ (intersection_moduli_pos Q hQ T hT),
    intersection_moduli_product]
  apply and_congr_right
  intro _hp
  constructor
  · intro h
    refine ⟨(mem_baseClasses Q A hA p).mp (h none),?_⟩
    intro t ht
    exact Finset.mem_singleton.mp (h (some ⟨t,ht⟩))
  · rintro ⟨hp,h⟩ i
    cases i with
    | none => exact (mem_baseClasses Q A hA p).mpr hp
    | some t => exact Finset.mem_singleton.mpr (h t.val t.property)

theorem intersectionResidues_card (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) : (intersectionResidues Q T A rho hT hQT).card=A.card := by
  rw [intersectionResidues,ErdosUnitLifts.crtNat_card _ _ _ (intersection_moduli_pos Q hQ T hT),Fintype.prod_option]
  change (baseClasses Q A).card*(∏ i : IntersectionIndex T,(intersectionClasses Q T A rho (some i)).card)=A.card
  have hp : (∏ i : IntersectionIndex T,(intersectionClasses Q T A rho (some i)).card)=1 := by
    apply Finset.prod_eq_one
    intro i _hi
    rfl
  rw [hp,mul_one]
  exact baseClasses_card Q A hA

theorem intersectionResidues_reduced (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (hAc : ∀ a∈A,a.Coprime Q) (hrho : ∀ t∈T,rho t≠0)
    (p : ℕ) (hp : p∈intersectionResidues Q T A rho hT hQT) :
    p<Q*(∏ t∈T,t) ∧ p.Coprime (Q*(∏ t∈T,t)) := by
  obtain ⟨hpM,hpA,hpT⟩ := (mem_intersectionResidues Q hQ T A rho hT hQT hA p).mp hp
  refine ⟨hpM,Nat.coprime_mul_iff_right.mpr ⟨?_,?_⟩⟩
  · have hu : IsUnit ((p%Q:ℕ):ZMod Q) := (ZMod.isUnit_iff_coprime _ _).mpr (hAc _ hpA)
    have he : ((p%Q:ℕ):ZMod Q)=(p:ZMod Q) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod p Q)
    rw [he] at hu
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  · apply Nat.coprime_prod_right_iff.mpr
    intro t ht
    let _ : Fact t.Prime := ⟨hT t ht⟩
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [hpT t ht]
    exact isUnit_iff_ne_zero.mpr (hrho t ht)

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open scoped BigOperators

theorem mod_mem_intersectionResidues (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (p : ℕ) :
    p%(Q*(∏ t∈T,t))∈intersectionResidues Q T A rho hT hQT ↔
      p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t := by
  let M := Q*(∏ t∈T,t)
  have hM : 0 < M := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  have hQd : Q∣M := dvd_mul_right Q _
  have hmodQ : (p%M)%Q=p%Q := Nat.mod_mod_of_dvd p hQd
  have htmod (t : ℕ) (ht : t∈T) : ((p%M:ℕ):ZMod t)=(p:ZMod t) := by
    have htd : t∣M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => t) ht) Q
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod_of_dvd p htd)
  rw [mem_intersectionResidues Q hQ T A rho hT hQT hA]
  change p%M<M ∧ (p%M)%Q∈A ∧ (∀ t∈T,((p%M:ℕ):ZMod t)=rho t) ↔ _
  simp only [Nat.mod_lt p hM,true_and,hmodQ]
  apply and_congr_right
  intro _h
  constructor <;> intro h t ht
  · simpa only [htmod t ht] using h t ht
  · simpa only [htmod t ht] using h t ht

lemma totient_prime_product (T : Finset ℕ) (hT : ∀ t∈T,t.Prime) :
    (∏ t∈T,t).totient=∏ t∈T,(t-1) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert t T ht ih =>
    have htp : t.Prime := hT t (Finset.mem_insert_self _ _)
    have hTp : ∀ p∈T,p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have hc : t.Coprime (∏ p∈T,p) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      apply htp.coprime_iff_not_dvd.mpr
      intro hd
      rcases (hTp p hp).eq_one_or_self_of_dvd t hd with he | he
      · exact htp.ne_one he
      · exact ht (he.symm ▸ hp)
    rw [Finset.prod_insert ht,Nat.totient_mul hc,Nat.totient_prime htp,ih hTp,Finset.prod_insert ht]

theorem totient_intersection_modulus (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    (Q*(∏ t∈T,t)).totient=Q.totient*(∏ t∈T,(t-1)) := by
  rw [Nat.totient_mul (Nat.coprime_prod_right_iff.mpr hQT),totient_prime_product T hT]

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagPrimePartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

lemma mem_AP_canonical (R V : ℝ) (M a p : ℕ) (ha : a<M) :
    p∈intervalPrimes R V M (a:ℤ) ↔ p∈intervalPrimes R V 1 0 ∧ p%M=a := by
  simp only [mem_intervalPrimes,Int.natCast_modEq_iff,Nat.ModEq,Nat.mod_eq_of_lt ha]
  have h1 : Int.ModEq (1:ℤ) (p:ℤ) 0 := by simp [Int.ModEq]
  simpa only [Nat.cast_one,h1,and_true] using (show
    (p.Prime ∧ R<(p:ℝ) ∧ (p:ℝ)≤R+V ∧ p%M=a) ↔
      (p.Prime ∧ R<(p:ℝ) ∧ (p:ℝ)≤R+V) ∧ p%M=a by tauto)

theorem intersectionPrimes_eq_biUnion (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    intersectionPrimes R V Q T A rho=
      (intersectionResidues Q T A rho hT hQT).biUnion
        (fun a => intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ)) := by
  ext p
  rw [intersectionPrimes,Finset.mem_filter,Finset.mem_biUnion]
  have hM : 0 < Q*(∏ t∈T,t) := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨p%(Q*(∏ t∈T,t)),(mod_mem_intersectionResidues Q hQ T A rho hT hQT hA p).mpr h,?_⟩
    exact (mem_AP_canonical R V _ _ p (Nat.mod_lt p hM)).mpr ⟨hp,rfl⟩
  · rintro ⟨a,ha,hp⟩
    have har := ((mem_intersectionResidues Q hQ T A rho hT hQT hA a).mp ha).1
    obtain ⟨hp,he⟩ := (mem_AP_canonical R V _ a p har).mp hp
    refine ⟨hp,(mod_mem_intersectionResidues Q hQ T A rho hT hQT hA p).mp ?_⟩
    rw [he]
    exact ha

lemma intersection_AP_disjoint (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    ((intersectionResidues Q T A rho hT hQT : Finset ℕ) : Set ℕ).Pairwise (fun a b =>
      Disjoint (intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ))
        (intervalPrimes R V (Q*(∏ t∈T,t)) (b:ℤ))) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  have har := ((mem_intersectionResidues Q hQ T A rho hT hQT hA a).mp ha).1
  have hbr := ((mem_intersectionResidues Q hQ T A rho hT hQT hA b).mp hb).1
  exact hab (((mem_AP_canonical R V _ a p har).mp hpa).2.symm.trans
    ((mem_AP_canonical R V _ b p hbr).mp hpb).2)

theorem intersectionPrimes_card (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    (intersectionPrimes R V Q T A rho).card=
      ∑ a∈intersectionResidues Q T A rho hT hQT,(intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ)).card := by
  rw [intersectionPrimes_eq_biUnion R V Q hQ T A rho hT hQT hA]
  exact Finset.card_biUnion (intersection_AP_disjoint R V Q hQ T A rho hT hQT hA)

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagIntersectionError
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz

lemma inverse_totient_intersection (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    (1:ℝ)/((Q*(∏ t∈T,t)).totient:ℝ)=
      (1/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
  rw [totient_intersection_modulus Q T hT hQT,Nat.cast_mul,Nat.cast_prod]
  have he : (∏ t∈T,((t-1:ℕ):ℝ))=∏ t∈T,((t:ℝ)-1) := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [Nat.cast_sub (hT t ht).one_le,Nat.cast_one]
  rw [he]
  simp only [one_div,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem intersection_prime_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ Q : ℕ,0 < Q →
      ∀ T A : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈T,t.Prime) → (∀ t∈T,Q.Coprime t) →
      (∀ a∈A,a<Q) → (∀ a∈A,a.Coprime Q) → (∀ t∈T,rho t≠0) →
      (Q*(∏ t∈T,t):ℕ) ≤ Real.exp (c*cubeHeight R) →
      |((intersectionPrimes R V Q T A rho).card:ℝ)-
        (((intervalPrimes R V 1 0).card:ℝ)*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1))| ≤
          (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_count_error
  refine ⟨c,C,X₀,hc,hC,hX₀,?_⟩
  intro R V hR hV hVR Q hQ T A rho hT hQT hA hAc hrho hmod
  let B := intersectionResidues Q T A rho hT hQT
  let M := Q*(∏ t∈T,t)
  let N : ℝ := (intervalPrimes R V 1 0).card
  have hM : 0 < M := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  have hB : B.card=A.card := intersectionResidues_card Q hQ T A rho hT hQT hA
  have hbound : ∀ a∈B,|((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)| ≤
      C*R*Real.exp (-c*cubeHeight R) := by
    intro a ha
    have hred := (intersectionResidues_reduced Q hQ T A rho hT hQT hA hAc hrho a ha).2
    exact hAP R V hR hV hVR M (a:ℤ) hM hred.isCoprime hmod
  have hmean : (∑ _a∈B,N/(M.totient:ℝ))=
      (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
    rw [Finset.sum_const,nsmul_eq_mul,hB]
    have hd := inverse_totient_intersection Q T hT hQT
    change 1/(M.totient:ℝ)=_ at hd
    calc
      _ = N*(A.card:ℝ)*(1/(M.totient:ℝ)) := by ring
      _ = _ := by rw [hd]; ring
  have hsum : (∑ a∈B,(((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)))=
      ((intersectionPrimes R V Q T A rho).card:ℝ)-
        (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
    rw [Finset.sum_sub_distrib,hmean,← Nat.cast_sum]
    congr 1
    exact_mod_cast (intersectionPrimes_card R V Q hQ T A rho hT hQT hA).symm
  change |((intersectionPrimes R V Q T A rho).card:ℝ)-
    (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1))| ≤ _
  rw [← hsum]
  calc
    _ ≤ ∑ a∈B,|((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a∈B,C*R*Real.exp (-c*cubeHeight R) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hB]; ring

end ErdosStoppedTagSieve


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

end NumberTheoryLean.SmallSieveFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_TagUnitSieveLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosStoppedTagSieve


lemma reciprocal_totient_density_le (p : ℕ) (hp : 2 ≤ p) : 1/((p:ℝ)-1) ≤ 2/(p:ℝ) := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  linarith





open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
open NumberTheoryLean
attribute [local instance] Classical.propDecidable

lemma actual_intersection_mass (R V : ℝ) (Q : ℕ) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) :
    BonferroniBlocks.intersectionMass (basePrimes R V Q A) (fun _ => 1)
      (fun t p => (p:ZMod t)=rho t) T = ((intersectionPrimes R V Q T A rho).card:ℝ) := by
  simp only [BonferroniBlocks.intersectionMass,BonferroniBlocks.intersectionValue,one_mul]
  have he : (basePrimes R V Q A).filter (fun p => ∀ t∈T,(p:ZMod t)=rho t)=intersectionPrimes R V Q T A rho := by
    ext p
    simp only [basePrimes,intersectionPrimes,Finset.mem_filter]
    tauto
  rw [← he]
  rw [Finset.natCast_card_filter (R := ℝ)]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> rfl

lemma actual_survivor_mass (R V : ℝ) (Q : ℕ) (S A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) :
    (∑ p∈basePrimes R V Q A, (1:ℝ)*BonferroniBlocks.survives S (fun t => (p:ZMod t)=rho t))=
      ((survivorPrimes R V Q S A rho).card:ℝ) := by
  simp only [BonferroniBlocks.survives,one_mul,survivorPrimes]
  rw [Finset.natCast_card_filter (R := ℝ)]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> rfl

theorem finite_tag_sieve_error_jb247_oai :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ Q : ℕ,0 < Q →
      ∀ S A : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈S,t.Prime) → (∀ t∈S,3 ≤ t) → (∀ t∈S,Q.Coprime t) →
      (∀ a∈A,a<Q) → (∀ a∈A,a.Coprime Q) → (∀ t∈S,rho t≠0) →
      ∀ u s : ℝ,3 ≤ u → 480024 ≤ s → (∀ t∈S,(t:ℝ) ≤ u) →
      (Q:ℝ)*u^s ≤ Real.exp (c*cubeHeight R) →
      let X : ℝ := ((intervalPrimes R V 1 0).card:ℝ)*(A.card:ℝ)/(Q.totient:ℝ)
      |((survivorPrimes R V Q S A rho).card:ℝ)-X*eulerWeight S| ≤
        X*eulerWeight S*Real.exp (-s/96)+(A.card:ℝ)*C*R*(u^s)*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := intersection_prime_error
  refine ⟨c,C,X₀,hc,hC,hX₀,?_⟩
  intro R V hR hV hVR Q hQ S A rho hPrime hOdd hQS hA hAc hrho u s hu hs hsize hlevel X
  let g : ℕ → ℝ := fun t => 1/((t:ℝ)-1)
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hR0 : 0 ≤ R := by have := hX₀.trans hR; linarith
  have hg : ∀ t∈S,0 ≤ g t := by
    intro t ht
    have htR : (3:ℝ) ≤ t := by exact_mod_cast hOdd t ht
    exact div_nonneg (by norm_num) (by linarith)
  have hdim : ∀ t∈S,g t ≤ 2/(t:ℝ) := fun t ht => reciprocal_totient_density_le t (by have := hOdd t ht; omega)
  have htwo : 2∈S → g 2 ≤ 1/2 := by intro h; have := hOdd 2 h; omega
  have hf := RealFundamentalSieve.fundamental_lemma (basePrimes R V Q A) (fun _ => 1)
    (fun _ _ => by norm_num) (fun t p => (p:ZMod t)=rho t) u s S X g
    (by linarith) hs hX hPrime hsize hg hdim htwo
  have hEuler : (∏ t∈S,(1-g t))=eulerWeight S := rfl
  rw [actual_survivor_mass,hEuler] at hf
  have hRem : ∀ d∈RealFundamentalSieve.levelDivisors S u s,
      |FundamentalBlockEstimate.integerRemainder (basePrimes R V Q A) (fun _ => 1)
        (fun t p => (p:ZMod t)=rho t) X g d| ≤ (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := by
    intro d hd
    obtain ⟨hdP,hdL⟩ := Finset.mem_filter.mp hd
    have hddiv := Nat.dvd_of_mem_divisors hdP
    have hsq := IntervalBoundingSieve.squarefree_primeSet_product S hPrime
    have hdsq := hsq.squarefree_of_dvd hddiv
    have hsub : d.primeFactors ⊆ S := by
      rw [← Nat.primeFactors_prod hPrime]
      exact Nat.primeFactors_mono hddiv hsq.ne_zero
    have hm : (Q*(∏ t∈d.primeFactors,t):ℕ) ≤ Real.exp (c*cubeHeight R) := by
      rw [Nat.prod_primeFactors_of_squarefree hdsq,Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hdL (Nat.cast_nonneg Q)).trans hlevel
    have hh := hAP R V hR hV hVR Q hQ d.primeFactors A rho
      (fun t ht => hPrime t (hsub ht)) (fun t ht => hQS t (hsub ht))
      hA hAc (fun t ht => hrho t (hsub ht)) hm
    unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    rw [actual_intersection_mass]
    exact hh
  have hSum : (∑ d∈RealFundamentalSieve.levelDivisors S u s,
      |FundamentalBlockEstimate.integerRemainder (basePrimes R V Q A) (fun _ => 1)
        (fun t p => (p:ZMod t)=rho t) X g d|) ≤
      (A.card:ℝ)*C*R*(u^s)*Real.exp (-c*cubeHeight R) := by
    calc
      _ ≤ ∑ _d∈RealFundamentalSieve.levelDivisors S u s,
        (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := Finset.sum_le_sum hRem
      _ = ((RealFundamentalSieve.levelDivisors S u s).card:ℝ)*((A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (u^s)*((A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R)) :=
        mul_le_mul_of_nonneg_right (SmallSieveFinite.realLevelDivisors_card_le S u s (by linarith)) (by positivity)
      _ = _ := by ring
  exact hf.trans (add_le_add le_rfl hSum)

end ErdosStoppedTagSieve



end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247_oai := @OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247_oai
