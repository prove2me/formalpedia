-- Prove2me | solution 1 for OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:34.343559+00:00
-- url     : https://prove2.me/submissions/77ea014c-784d-4f16-a8ae-ee2a09830fb3

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
import Theorems.Thm_OAI_Erdos970_ErdosStoppedTagSieve_finite_tag_sieve_error_jb247

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

theorem radical_pos (D : ℕ) : 0 < radical D :=
  Finset.prod_pos (fun _ ht => Nat.pos_of_mem_primeFactors ht)

theorem radical_dvd (D : ℕ) : radical D ∣ D := Nat.prod_primeFactors_dvd D

theorem radical_primeFactors (D : ℕ) : (radical D).primeFactors = D.primeFactors :=
  Nat.primeFactors_prod_primeFactors D

theorem totient_radical (D : ℕ) :
    (radical D).totient = ∏ t ∈ D.primeFactors, (t - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, radical_primeFactors]
  change radical D / radical D * _ = _
  rw [Nat.div_self (radical_pos D), one_mul]

theorem totient_lift_modulus (D : ℕ) (hD : 0 < D) :
    (D * radical D).totient = D * (radical D).totient := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  rw [Nat.primeFactors_mul hD.ne' (radical_pos D).ne', radical_primeFactors,
    Finset.union_self, totient_radical]
  change D * radical D / radical D * _ = _
  rw [Nat.mul_div_cancel D (radical_pos D)]

theorem primeIndex_coprime (D : ℕ) :
    Pairwise (fun t u : PrimeIndex D => Nat.Coprime t.val u.val) := by
  intro t u hne
  exact (Nat.prime_of_mem_primeFactors t.property).coprime_iff_not_dvd.mpr (by
    intro h
    have he := (Nat.prime_of_mem_primeFactors u.property).eq_one_or_self_of_dvd _ h
    rcases he with he | he
    · exact (Nat.prime_of_mem_primeFactors t.property).ne_one he
    · exact hne (Subtype.ext he))

theorem affine_eq_iff (t : ℕ) (n B a : ℤ) (hB : IsUnit (B : ZMod t))
    (x : ZMod t) :
    (n : ZMod t) + B * x = a ↔ x = (B : ZMod t)⁻¹ * (a - n) := by
  constructor
  · intro h
    calc
      x = (B : ZMod t)⁻¹ * (B * x) := by rw [← mul_assoc, ZMod.inv_mul_of_unit _ hB, one_mul]
      _ = (B : ZMod t)⁻¹ * (a - n) := by congr 1; linear_combination h
  · intro h
    rw [h, ← mul_assoc, ZMod.mul_inv_of_unit _ hB, one_mul]
    ring

theorem localAllowed_card (t : ℕ) [NeZero t] (n B a : ℤ)
    (hB : IsUnit (B : ZMod t)) : (localAllowed t n B a).card = t - 1 := by
  have he : localAllowed t n B a = Finset.univ.erase ((B : ZMod t)⁻¹ * (a - n)) := by
    ext x
    simp [localAllowed, affine_eq_iff t n B a hB]
  rw [he, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

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

theorem allowedK_card (D : ℕ) (n B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B : ZMod D)) :
    (allowedK D n B a).card = (radical D).totient := by
  let (t : PrimeIndex D) : NeZero t.val := ⟨(Nat.pos_of_mem_primeFactors t.property).ne'⟩
  let m := fun t : PrimeIndex D => t.val
  let E := fun t : PrimeIndex D => localAllowed t.val n B (a t.val)
  have hm : (∏ t : PrimeIndex D, m t) = radical D := by
    exact Finset.prod_coe_sort D.primeFactors (fun t => t)
  have hpos : 0 < ∏ t : PrimeIndex D, m t := hm ▸ radical_pos D
  have he : allowedK D n B a = crtNat m (primeIndex_coprime D) E := by
    ext k
    rw [mem_crtNat m (primeIndex_coprime D) E hpos]
    simp only [allowedK, Finset.mem_filter, Finset.mem_range, hm]
    simp only [E, localAllowed, Finset.mem_filter, Finset.mem_univ, true_and,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    apply and_congr_right
    intro _
    constructor
    · intro h t
      exact h t.val t.property
    · intro h t ht
      exact h ⟨t,ht⟩
  rw [he, crtNat_card m (primeIndex_coprime D) E hpos, totient_radical]
  calc
    (∏ t : PrimeIndex D, (E t).card) = ∏ t : PrimeIndex D, (t.val - 1) := by
      apply Finset.prod_congr rfl
      intro t _
      apply localAllowed_card
      have hd : t.val ∣ D := Nat.dvd_of_mem_primeFactors t.property
      simpa using hB.map (ZMod.castHom hd (ZMod t.val))
    _ = _ := Finset.prod_coe_sort D.primeFactors (fun t => t - 1)

end ErdosUnitLifts

end

section

open scoped BigOperators
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

theorem baseResidue_lt (D : ℕ) (hD : 0 < D) (A B : ℤ) : baseResidue D A B < D := by
  let : NeZero D := ⟨hD.ne'⟩
  exact ZMod.val_lt _

theorem baseResidue_integral (D : ℕ) (hD : 0 < D) (A B : ℤ)
    (hB : IsUnit (B : ZMod D)) : (D : ℤ) ∣ A + B * baseResidue D A B := by
  let : NeZero D := ⟨hD.ne'⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mp
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, baseResidue, ZMod.natCast_zmod_val]
  calc
    (A : ZMod D) + B * (-A * (B : ZMod D)⁻¹) = A - A * (B * (B : ZMod D)⁻¹) := by ring
    _ = 0 := by rw [ZMod.mul_inv_of_unit _ hB]; ring

theorem integral_iff_base_mod (D p0 : ℕ) (hp0 : p0 < D) (A B : ℤ)
    (hB : IsUnit (B : ZMod D)) (h0 : (D : ℤ) ∣ A + B * p0) (p : ℕ) :
    (D : ℤ) ∣ A + B * p ↔ p % D = p0 := by
  have hz0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hz0
  have hh : (D : ℤ) ∣ A + B * p ↔ (p : ZMod D) = p0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    constructor
    · intro hp
      apply hB.mul_left_cancel
      linear_combination hp - hz0
    · intro hp
      simpa only [hp] using hz0
  rw [hh, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp0]

theorem base_coprime (D p0 : ℕ) (A B : ℤ)
    (hA : IsUnit (A : ZMod D)) (h0 : (D : ℤ) ∣ A + B * p0) :
    Nat.Coprime p0 D := by
  apply (ZMod.isUnit_iff_coprime p0 D).mp
  have hz0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hz0
  have he : (B : ZMod D) * p0 = -A := by linear_combination hz0
  apply isUnit_of_mul_isUnit_right (x := (B : ZMod D))
  rw [he]
  exact hA.neg

theorem actualN_lift (D : ℕ) (hD : 0 < D) (A B : ℤ) (p0 k : ℕ) :
    actualN D A B (p0 + D * k) = actualN D A B p0 + B * k := by
  unfold actualN
  have hn : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : A + B * (p0 + D * k : ℕ) = A + B * p0 + (B * k) * D := by push_cast <;> ring
  rw [he, Int.add_mul_ediv_right _ _ hn]

theorem lift_coprime (D p0 k : ℕ) (hp : Nat.Coprime p0 D) :
    Nat.Coprime (p0 + D * k) (D * radical D) := by
  have hd : Nat.Coprime (p0 + D * k) D :=
    (Nat.coprime_add_mul_left_left p0 D k).mpr hp
  exact Nat.coprime_mul_iff_right.mpr ⟨hd, Nat.Coprime.coprime_dvd_right (radical_dvd D) hd⟩

theorem canonical_lift_iff (D p0 p : ℕ) (hD : 0 < D) (hp0 : p0 < D) :
    p < D * radical D ∧ p % D = p0 ↔
      ∃ k < radical D, p0 + D * k = p := by
  constructor
  · rintro ⟨hp,hm⟩
    refine ⟨p / D, ?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hD).mpr (by simpa [Nat.mul_comm] using hp)
    · simpa only [hm] using Nat.mod_add_div p D
  · rintro ⟨k,hk,rfl⟩
    constructor
    · calc
        p0 + D * k < D + D * k := Nat.add_lt_add_right hp0 _
        _ = D * (k + 1) := by ring
        _ ≤ D * radical D := Nat.mul_le_mul_left D hk
    · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp0]

theorem actualClasses_eq_lifts (D p0 : ℕ) (hD : 0 < D) (hp0 : p0 < D)
    (A B : ℤ) (a : ℕ → ℤ) (hB : IsUnit (B : ZMod D))
    (h0 : (D : ℤ) ∣ A + B * p0) :
    actualClasses D A B a =
      (allowedK D (actualN D A B p0) B a).image (fun k => p0 + D * k) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hi,ha⟩ := Finset.mem_filter.mp hp
    obtain ⟨k,hk,hkp⟩ := (canonical_lift_iff D p0 p hD hp0).mp
      ⟨Finset.mem_range.mp hp, (integral_iff_base_mod D p0 hp0 A B hB h0 p).mp hi⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩, hkp⟩
    intro t ht
    have hh := ha t ht
    rw [← hkp, actualN_lift D hD] at hh
    exact hh
  · intro hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hk,ha⟩ := Finset.mem_filter.mp hk
    have hc := (canonical_lift_iff D p0 (p0 + D * k) hD hp0).mpr
      ⟨k, Finset.mem_range.mp hk, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hc.1, ?_, ?_⟩
    · exact (integral_iff_base_mod D p0 hp0 A B hB h0 _).mpr hc.2
    · intro t ht
      rw [actualN_lift D hD]
      exact ha t ht

theorem actualClasses_card (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B : ZMod D)) :
    (actualClasses D A B a).card = (radical D).totient := by
  rw [actualClasses_eq_lifts D (baseResidue D A B) hD (baseResidue_lt D hD A B)
    A B a hB (baseResidue_integral D hD A B hB)]
  rw [Finset.card_image_of_injective]
  · exact allowedK_card D (actualN D A B (baseResidue D A B)) B a hB
  · intro k l h
    exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel h)

theorem actualClasses_reduced (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hA : IsUnit (A : ZMod D)) (hB : IsUnit (B : ZMod D))
    (p : ℕ) (hp : p ∈ actualClasses D A B a) :
    p < D * radical D ∧ Nat.Coprime p (D * radical D) := by
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  rw [actualClasses_eq_lifts D (baseResidue D A B) hD (baseResidue_lt D hD A B)
    A B a hB (baseResidue_integral D hD A B hB)] at hp
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨hrange, lift_coprime D _ k
    (base_coprime D _ A B hA (baseResidue_integral D hD A B hB))⟩

theorem intCast_isUnit_of_natAbs_coprime (D : ℕ) (B : ℤ)
    (hB : Nat.Coprime B.natAbs D) : IsUnit (B : ZMod D) := by
  have hh := (ZMod.isUnit_iff_coprime B.natAbs D).mpr hB
  have ha : IsUnit ((|B| : ℤ) : ZMod D) := by
    simpa only [← Int.natCast_natAbs, Int.cast_natCast] using hh
  rcases le_total 0 B with hp | hn
  · simpa only [abs_of_nonneg hp] using ha
  · have ht : IsUnit (-(B : ZMod D)) := by simpa only [abs_of_nonpos hn, Int.cast_neg] using ha
    simpa only [neg_neg] using ht.neg

end ErdosUnitLifts

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

lemma inv_log_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t:ℝ => 1/Real.log t) volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop)

lemma logarithmicIntegral_sub {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    logarithmicIntegral v-logarithmicIntegral u = ∫ t in u..v, 1/Real.log t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (inv_log_intervalIntegrable (by norm_num) hu) (inv_log_intervalIntegrable hu huv)
  unfold logarithmicIntegral
  linarith

lemma logarithmicIntegral_sub_lower {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (v-u)/Real.log v ≤ logarithmicIntegral v-logarithmicIntegral u := by
  have hv1 : 1 < v := by linarith
  rw [logarithmicIntegral_sub hu huv]
  calc
    _ = ∫ _t in u..v, 1/Real.log v := by simp <;> ring
    _ ≤ _ := intervalIntegral.integral_mono_on huv (by simp)
      (inv_log_intervalIntegrable hu huv) (fun t ht => by
        have ht1 : 1 < t := by linarith [ht.1]
        have hl : Real.log t ≤ Real.log v := Real.log_le_log (by linarith) ht.2
        exact one_div_le_one_div_of_le (Real.log_pos ht1) hl)

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

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz

lemma moving_lower_ge_self {w : ℝ} (hw : 1 ≤ w) :
    w ≤ Real.exp (w^((1:ℝ)/4)*Real.log w) := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hp : 1 ≤ w^((1:ℝ)/4) := Real.one_le_rpow hw (by norm_num)
  have hl : 0 ≤ Real.log w := Real.log_nonneg hw
  calc
    w = Real.exp (Real.log w) := (Real.exp_log hw0).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hp) hl])

lemma cubeHeight_moving_lower {w R : ℝ} (hw : 3 ≤ w)
    (hR : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R) :
    w^((1:ℝ)/12) ≤ cubeHeight R := by
  have hw0 : 0 < w := by linarith
  have hl : 1 ≤ Real.log w :=
    ((Real.lt_log_iff_exp_lt hw0).mpr (Real.exp_one_lt_three.trans_le hw)).le
  have hlog := Real.log_le_log (Real.exp_pos (w^((1:ℝ)/4)*Real.log w)) hR
  rw [Real.log_exp] at hlog
  have hp : 0 ≤ w^((1:ℝ)/4) := Real.rpow_nonneg hw0.le _
  have hs : w^((1:ℝ)/4) ≤ Real.log R := by nlinarith [mul_nonneg hp (sub_nonneg.mpr hl)]
  calc
    w^((1:ℝ)/12) = (w^((1:ℝ)/4))^((1:ℝ)/3) := by
      rw [← Real.rpow_mul hw0.le]
      norm_num
    _ ≤ cubeHeight R := Real.rpow_le_rpow hp hs (by norm_num)

theorem eventually_moving_exponential_domination (A b K c : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (_hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,1 ≤ P →
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      w^A*P^b ≤ Real.exp (c*cubeHeight R) := by
  have hpoly := Real.tendsto_log_atTop.eventually
    (eventually_polynomial_le_exp ((A+b*K)/c) 3 (by norm_num : (0:ℝ)<1/12))
  filter_upwards [eventually_ge_atTop (3:ℝ),hpoly] with w hw hpolyw
  refine ⟨hw,?_⟩
  intro P R hP hPcap hR
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hl1 := hpolyw.1
  have hLP : Real.log P ≤ K*(Real.log w)^3 := by
    have h := Real.log_le_log hP0 hPcap
    simpa only [Real.log_exp] using h
  have hLsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hLcube : Real.log w ≤ (Real.log w)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sq_nonneg (Real.log w))]
  have hcost : A*Real.log w+b*Real.log P ≤ (A+b*K)*(Real.log w)^3 := by
    have ha := mul_le_mul_of_nonneg_left hLcube hA
    have hh := mul_le_mul_of_nonneg_left hLP hb
    nlinarith
  have hy := cubeHeight_moving_lower hw hR
  have he : Real.exp ((1/12:ℝ)*Real.log w)=w^((1:ℝ)/12) := by
    rw [Real.rpow_def_of_pos hw0]
    congr 1
    ring
  have hpol : ((A+b*K)/c)*(Real.log w)^3 ≤ cubeHeight R := by
    have hz : ((A+b*K)/c)*(Real.log w)^3 ≤ w^((1:ℝ)/12) := by
      simpa only [he] using hpolyw.2
    exact hz.trans hy
  have hh := mul_le_mul_of_nonneg_left hpol hc.le
  have hEq : c*(((A+b*K)/c)*(Real.log w)^3)=(A+b*K)*(Real.log w)^3 := by
    field_simp
  rw [hEq] at hh
  rw [Real.rpow_def_of_pos hw0,Real.rpow_def_of_pos hP0,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem eventually_moving_error (A b K c B eps : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hK : 0 ≤ K) (hc : 0 < c)
    (hB : 0 ≤ B) (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,1 ≤ P →
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      B*w^A*P^b*Real.log R*Real.exp (-c*cubeHeight R) ≤ eps := by
  have hdom := eventually_moving_exponential_domination A b K (c/2) hA hb hK (by positivity)
  have ht : Tendsto (fun y : ℝ => B*y^3*Real.exp (-(c/2)*y)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3:ℝ) (c/2) (by positivity)).const_mul B
  obtain ⟨y₀,hy₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  have hp : ∀ᶠ w : ℝ in atTop,y₀ ≤ w^((1:ℝ)/12) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/12)).eventually (eventually_ge_atTop y₀)
  filter_upwards [hdom,hp] with w hw hwy
  refine ⟨hw.1,?_⟩
  intro P R hP hPcap hR
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith [hw.1])).trans hR
  have hR1 : 1 ≤ R := by linarith [hw.1]
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR1
  have he := hw.2 P R hP hPcap hR
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB) hlog)
    (Real.exp_pos (-c*cubeHeight R)).le
  have hrate := hy₀ (cubeHeight R) (hwy.trans (cubeHeight_moving_lower hw.1 hR))
  have hEq : B*Real.exp ((c/2)*cubeHeight R)*Real.log R*Real.exp (-c*cubeHeight R)=
      B*(cubeHeight R)^3*Real.exp (-(c/2)*cubeHeight R) := by
    rw [cubeHeight_pow_three hR1]
    have hh : Real.exp ((c/2)*cubeHeight R)*Real.exp (-c*cubeHeight R)=Real.exp (-(c/2)*cubeHeight R) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = B*Real.log R*(Real.exp ((c/2)*cubeHeight R)*Real.exp (-c*cubeHeight R)) := by ring
      _ = _ := by rw [hh]
  rw [hEq] at hprod
  have hleft : B*w^A*P^b*Real.log R*Real.exp (-c*cubeHeight R)=
      B*(w^A*P^b)*Real.log R*Real.exp (-c*cubeHeight R) := by ring
  rw [hleft]
  exact hprod.trans hrate.le

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz

lemma eventually_cutoff_dominates (a K : ℝ) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ w^a < Real.exp (K*(Real.log w)^3) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 ((a+1)/K)))] with w hw hL
  refine ⟨hw,?_⟩
  have hw0 : 0 < w := by linarith
  have hL1 : 1 ≤ Real.log w := (le_max_left _ _).trans hL
  have haK : (a+1)/K ≤ Real.log w := (le_max_right _ _).trans hL
  have hKL : a+1 ≤ K*Real.log w := by
    have hh := (div_le_iff₀ hK).mp haK
    nlinarith
  have hLsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hKsq : a+1 ≤ K*(Real.log w)^2 := hKL.trans (mul_le_mul_of_nonneg_left hLsq hK.le)
  have hcube : (a+1)*Real.log w ≤ K*(Real.log w)^3 := by
    calc
      _ ≤ (K*(Real.log w)^2)*Real.log w := mul_le_mul_of_nonneg_right hKsq (by linarith)
      _ = _ := by ring
  rw [Real.rpow_def_of_pos hw0]
  apply Real.exp_lt_exp.mpr
  nlinarith

lemma eventually_cutoff_le_subbin (K : ℝ) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → P ≤ R := by
  have hp := Real.tendsto_log_atTop.eventually
    (eventually_polynomial_le_exp K 3 (by norm_num : (0:ℝ)<1/4))
  filter_upwards [eventually_ge_atTop (3:ℝ),hp] with w hw hpw
  refine ⟨hw,?_⟩
  intro P R hP hR
  have hw0 : 0 < w := by linarith
  have he : Real.exp ((1/4:ℝ)*Real.log w)=w^((1:ℝ)/4) := by
    rw [Real.rpow_def_of_pos hw0]
    congr 1
    ring
  have hpoly : K*(Real.log w)^3 ≤ w^((1:ℝ)/4) := by simpa only [he] using hpw.2
  have hlog := hpw.1
  have hpow : 0 ≤ w^((1:ℝ)/4) := Real.rpow_nonneg hw0.le _
  have hh : K*(Real.log w)^3 ≤ w^((1:ℝ)/4)*Real.log w := by
    nlinarith [mul_nonneg hpow (sub_nonneg.mpr hlog)]
  exact (hP.trans (Real.exp_le_exp.mpr hh)).trans hR

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagSmallPrimeData
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve
open ErdosUnitLifts

lemma integral_mod_lift_iff (D : ℕ) (A B : ℤ) (p : ℕ) :
    (D:ℤ) ∣ A+B*(p%(D*radical D):ℕ) ↔ (D:ℤ) ∣ A+B*p := by
  have hp : ((p%(D*radical D):ℕ):ZMod D)=(p:ZMod D) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    exact Nat.mod_mod_of_dvd p (dvd_mul_right D (radical D))
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [hp]

lemma actualN_mod_lift (D : ℕ) (hD : 0 < D) (A B : ℤ) (p t : ℕ)
    (ht : t∈D.primeFactors) :
    (actualN D A B (p%(D*radical D)):ZMod t)=(actualN D A B p:ZMod t) := by
  have he : p%(D*radical D)+D*(radical D*(p/(D*radical D)))=p := by
    simpa only [Nat.mul_assoc] using Nat.mod_add_div p (D*radical D)
  have hn := actualN_lift D hD A B (p%(D*radical D)) (radical D*(p/(D*radical D)))
  rw [he] at hn
  have htr : t∣radical D := Finset.dvd_prod_of_mem (fun t => t) ht
  have hz : (radical D:ZMod t)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr htr
  rw [hn]
  push_cast
  simp [hz]

theorem mem_actualClasses_mod_iff (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ) (p : ℕ) :
    p%(D*radical D)∈actualClasses D A B a ↔
      (D:ℤ)∣A+B*p ∧ ∀ t∈D.primeFactors,(actualN D A B p:ZMod t)≠a t := by
  have hQ : 0 < D*radical D := Nat.mul_pos hD (radical_pos D)
  simp only [actualClasses,Finset.mem_filter,Finset.mem_range,Nat.mod_lt p hQ,true_and,
    integral_mod_lift_iff]
  apply and_congr_right
  intro _h
  constructor <;> intro h t ht
  · simpa only [actualN_mod_lift D hD A B p t ht] using h t ht
  · simpa only [actualN_mod_lift D hD A B p t ht] using h t ht

end ErdosStoppedTagSieve



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

lemma coefficient_cast_zero {t d0 : ℕ} {B : ℤ}
    (hprofile : t∣B.natAbs ↔ t∣d0) (ht : t∣d0) : (B:ZMod t)=0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd B t).mpr (Int.natCast_dvd.mpr (hprofile.mpr ht))

lemma coefficient_unit_of_not_dvd {t d0 : ℕ} (ht : t.Prime) (B : ℤ)
    (hprofile : t∣B.natAbs ↔ t∣d0) (hnot : ¬t∣d0) : IsUnit (B:ZMod t) :=
  intCast_isUnit_of_natAbs_coprime t B
    ((ht.coprime_iff_not_dvd.mpr (fun hd => hnot (hprofile.mp hd))).symm)

theorem signed_coefficient_profile (P : ℝ) (q d0 ell : ℕ) (m : ℤ)
    (hq : ∀ t∈smallPrimeSet P,q.Coprime t) (hell : ell.Prime) (hellP : P<(ell:ℝ))
    (hm : m.natAbs=d0*ell) :
    ∀ t∈smallPrimeSet P,t∣((q:ℤ)*m).natAbs ↔ t∣d0 := by
  intro t ht
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp ht
  have htq : ¬t∣q := htp.coprime_iff_not_dvd.mp (hq t ht).symm
  have hte : ¬t∣ell := by
    intro hd
    rcases hell.eq_one_or_self_of_dvd t hd with he | he
    · exact htp.ne_one he
    · have her : (t:ℝ)=ell := by exact_mod_cast he
      linarith
  simp only [Int.natAbs_mul,Int.natAbs_natCast,hm,htp.dvd_mul,htq,hte,false_or,or_false]

theorem denominator_coefficient_coprime (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0) : B.natAbs.Coprime D := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro t htp htD htB
  have htR : (t:ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD htD
  have htS : t∈smallPrimeSet P := (mem_smallPrimeSet P t).mpr ⟨htp,htR.trans_lt hDP⟩
  have htd0 := (hprofile t htS).mp htB
  have he := hsupport t (Nat.mem_primeFactors.mpr ⟨htp,htd0,hd0.ne'⟩)
  exact (Finset.mem_filter.mp he).2.1 htD

lemma restricted_coefficient_unit (P : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (t : ℕ) (ht : t∈restrictedPrimes P D A residue d0) : IsUnit (B:ZMod t) := by
  obtain ⟨htE,htd⟩ := Finset.mem_filter.mp ht
  have htS := (Finset.mem_filter.mp htE).1
  exact coefficient_unit_of_not_dvd ((mem_smallPrimeSet P t).mp htS).1 B (hprofile t htS) htd

lemma forbiddenClass_ne_zero (P : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (t : ℕ) (ht : t∈restrictedPrimes P D A residue d0) : forbiddenClass D A B residue t≠0 := by
  have htE := (Finset.mem_filter.mp ht).1
  obtain ⟨htS,_,hrhs⟩ := Finset.mem_filter.mp htE
  let _ : Fact t.Prime := ⟨((mem_smallPrimeSet P t).mp htS).1⟩
  have hB := restricted_coefficient_unit P D A B residue d0 hprofile t ht
  exact mul_ne_zero (inv_ne_zero (isUnit_iff_ne_zero.mp hB)) hrhs

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagRelativeAlgebra
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve

open ErdosUnitLifts

lemma actualClasses_fraction_real (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B:ZMod D)) :
    ((actualClasses D A B a).card:ℝ)/((D*radical D).totient:ℝ)=1/(D:ℝ) := by
  rw [actualClasses_card D hD A B a hB,totient_lift_modulus D hD,Nat.cast_mul]
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  have ht : ((radical D).totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (radical_pos D)).ne'
  field_simp

lemma actualClasses_card_le (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B:ZMod D)) : (actualClasses D A B a).card ≤ D := by
  rw [actualClasses_card D hD A B a hB]
  exact (Nat.totient_le _).trans (Nat.le_of_dvd hD (radical_dvd D))

lemma lift_modulus_bound {w Cs : ℝ} (hw : 0 < w) {D : ℕ} (hD : 0 < D)
    (hDw : (D:ℝ) ≤ w^Cs) : (D*radical D:ℕ) ≤ w^(2*Cs) := by
  have hrad : (radical D:ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD (radical_dvd D)
  rw [Nat.cast_mul]
  calc
    _ ≤ w^Cs*w^Cs := mul_le_mul hDw (hrad.trans hDw) (Nat.cast_nonneg _) (Real.rpow_nonneg hw.le _)
    _ = _ := by rw [← Real.rpow_add hw]; congr 1; ring

lemma relative_remainder_bound (A D B N W Z P L R C u e xi : ℝ)
    (_hA0 : 0 ≤ A) (hAD : A ≤ D) (hD : 0 < D) (hDB : D ≤ B)
    (hZ : 0 < Z) (hP : 0 < P) (hL : 0 < L) (hR : 0 < R)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (hxi : 0 < xi)
    (hN : xi*R/(64*Z*L) ≤ N) (hW : 1/P ≤ W) :
    A*C*R*u*e ≤ (N/D)*W*((64*C/xi)*B^2*Z*P*u*L*e) := by
  have hN0 : 0 < N := (by positivity : 0 < xi*R/(64*Z*L)).trans_le hN
  have hB : 0 < B := hD.trans_le hDB
  have hAD' : A*D ≤ B^2 := by
    have hh := mul_le_mul (hAD.trans hDB) hDB hD.le hB.le
    simpa only [pow_two] using hh
  have hN' : xi*R ≤ 64*Z*L*N := by
    have hh := (div_le_iff₀ (show 0 < 64*Z*L by positivity)).mp hN
    nlinarith
  have hW' : 1 ≤ P*W := by
    have hh := (div_le_iff₀ hP).mp hW
    simpa only [mul_comm] using hh
  have hChain : A*D*(xi*R) ≤ B^2*(64*Z*L*N)*(P*W) := by
    calc
      _ ≤ B^2*(xi*R) := mul_le_mul_of_nonneg_right hAD' (by positivity)
      _ ≤ B^2*(64*Z*L*N) := mul_le_mul_of_nonneg_left hN' (sq_nonneg B)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hW'
  have hh := mul_le_mul_of_nonneg_right hChain (mul_nonneg (mul_nonneg hC hu) he)
  apply (mul_le_mul_iff_left₀ (mul_pos hD hxi)).mp
  have hleft : (A*C*R*u*e)*(D*xi)=(A*D*(xi*R))*(C*u*e) := by ring
  have hright : ((N/D)*W*((64*C/xi)*B^2*Z*P*u*L*e))*(D*xi)=
      (B^2*(64*Z*L*N)*(P*W))*(C*u*e) := by
    field_simp
  rw [hleft,hright]
  exact hh

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagSubbinPrimeLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma subbin_geometry (Cs xi w R V : ℝ) (hCs : 0 ≤ Cs) (hxi : 0 < xi) (hw : 3 ≤ w)
    (hR : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R)
    (hlo : xi/(16*w^(2*Cs+10)) ≤ V/R) (hhi : V/R ≤ w^(-(2*Cs+10))) :
    0 < R ∧ 0 < V ∧ V ≤ R := by
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hw0 : 0 < w := by linarith
  have hlow : (xi/(16*w^(2*Cs+10)))*R ≤ V := (le_div_iff₀ hR0).mp hlo
  have hlow0 : 0 < (xi/(16*w^(2*Cs+10)))*R := by positivity
  have hwle : w^(-(2*Cs+10)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hvup := (div_le_iff₀ hR0).mp hhi
  exact ⟨hR0,hlow0.trans_le hlow,hvup.trans ((mul_le_mul_of_nonneg_right hwle hR0.le).trans_eq (one_mul R))⟩

theorem moving_subbin_prime_lower (Cs xi : ℝ) (hCs : 0 ≤ Cs) (hxi : 0 < xi) :
    ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w R V : ℝ,w₀ ≤ w →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      0 < R ∧ 0 < V ∧ V ≤ R ∧
      V/(4*Real.log R) ≤ ((intervalPrimes R V 1 0).card:ℝ) ∧
      0 < ((intervalPrimes R V 1 0).card:ℝ) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_li_error
  have hRate := eventually_moving_error (2*Cs+10) 0 0 c 1 (xi/(64*C))
    (by linarith) (by norm_num) (by norm_num) hc (by norm_num) (by positivity)
  obtain ⟨W,hW⟩ := eventually_atTop.mp hRate
  refine ⟨max 3 (max W X₀),le_max_left _ _,?_⟩
  intro w R V hw hR hlo hhi
  have hw3 : 3 ≤ w := (le_max_left _ _).trans hw
  have hwW : W ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwX : X₀ ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw
  have hw0 : 0 < w := by linarith
  obtain ⟨hR0,hV0,hVR⟩ := subbin_geometry Cs xi w R V hCs hxi hw3 hR hlo hhi
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith)).trans hR
  have hR3 : 3 ≤ R := hw3.trans hRw
  have hL : 0 < Real.log R := Real.log_pos (by linarith)
  have hp : 0 < w^(2*Cs+10) := Real.rpow_pos_of_pos hw0 _
  have hsmall := (hW w hwW).2 1 R (by norm_num) (by simp) hR
  simp only [Real.one_rpow,mul_one,one_mul] at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4*C*R/(w^(2*Cs+10)) by positivity)
  have hleft : (4*C*R/(w^(2*Cs+10)))*(w^(2*Cs+10)*Real.log R*Real.exp (-c*cubeHeight R))=
      4*C*R*Real.log R*Real.exp (-c*cubeHeight R) := by field_simp
  have hright : (4*C*R/(w^(2*Cs+10)))*(xi/(64*C))=(xi/(16*w^(2*Cs+10)))*R := by
    field_simp
    ring
  rw [hleft,hright] at hmul
  have hlow := (le_div_iff₀ hR0).mp hlo
  have herror : C*R*Real.exp (-c*cubeHeight R) ≤ V/(4*Real.log R) := by
    apply (le_div_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    convert hmul.trans hlow using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmod1 : ((1:ℕ):ℝ) ≤ Real.exp (c*cubeHeight R) := by
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (mul_nonneg hc.le (cubeHeight_pos (X := R) (by linarith)).le)
  have hErr := hAP R V (hwX.trans hRw) hV0.le hVR 1 0 (by norm_num) (by norm_num) hmod1
  simp only [Nat.totient_one,Nat.cast_one,div_one] at hErr
  have hMain : V/Real.log (R+V) ≤ logarithmicIntegral (R+V)-logarithmicIntegral R := by
    simpa only [add_sub_cancel_left] using logarithmicIntegral_sub_lower (by linarith : 2 ≤ R) (show R ≤ R+V by linarith)
  have hLog : Real.log (R+V) ≤ 2*Real.log R := by
    have he := Real.log_le_log (show 0 < R+V by linarith) (show R+V ≤ R^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using he
  have hLogPos : 0 < Real.log (R+V) := Real.log_pos (by linarith)
  have hLI : V/(2*Real.log R) ≤ logarithmicIntegral (R+V)-logarithmicIntegral R :=
    (div_le_div_of_nonneg_left hV0.le hLogPos hLog).trans hMain
  have hsplit : V/(2*Real.log R)=V/(4*Real.log R)+V/(4*Real.log R) := by ring
  rw [hsplit] at hLI
  have hlower := (abs_le.mp hErr).1
  have hN : V/(4*Real.log R) ≤ ((intervalPrimes R V 1 0).card:ℝ) := by linarith
  exact ⟨hR0,hV0,hVR,hN,(by positivity : 0 < V/(4*Real.log R)).trans_le hN⟩

end ErdosStoppedTagSieve


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

open scoped BigOperators

lemma shifted_nonneg (k : ℕ) : 0 ≤ (1:ℝ)-1/((k:ℝ)+2) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hh : (0:ℝ) < (k:ℝ)+2 := by positivity
  have h := (div_le_one hh).mpr (show (1:ℝ) ≤ (k:ℝ)+2 by linarith)
  linarith

lemma shifted_le_one (k : ℕ) : (1:ℝ)-1/((k:ℝ)+2) ≤ 1 := by
  have : (0:ℝ) ≤ 1/((k:ℝ)+2) := by positivity
  linarith

lemma shifted_product (N : ℕ) :
    (∏ k∈Finset.range N,((1:ℝ)-1/((k:ℝ)+2)))=1/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ,ih]
    push_cast
    have h1 : (N:ℝ)+1 ≠ 0 := by positivity
    have h2 : (N:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

theorem eulerWeight_lower (P : ℝ) (hP : 3 ≤ P) (S : Finset ℕ)
    (hS : ∀ p∈S,3 ≤ p ∧ (p:ℝ) ≤ P) : 1/P ≤ eulerWeight S := by
  classical
  have hP0 : 0 ≤ P := by linarith
  have hf : 3 ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (by exact_mod_cast hP)
  let N := ⌊P⌋₊-2
  have hsub : (S.image (fun p : ℕ => (p-3:ℕ)) : Finset ℕ) ⊆ Finset.range N := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    have hpl : p ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (hS p hp).2
    have hp3 := (hS p hp).1
    apply Finset.mem_range.mpr
    dsimp [N]
    omega
  have hnP : (N:ℝ)+1 ≤ P := by
    dsimp [N]
    rw [Nat.cast_sub (by omega)]
    have hfl := Nat.floor_le hP0
    norm_num only [Nat.cast_ofNat]
    linarith
  have hprod := Finset.prod_le_prod_of_subset_of_le_one hsub
    (fun k _ => shifted_nonneg k) (fun k _ _ => shifted_le_one k)
  have himage : (∏ k∈(S.image (fun p : ℕ => (p-3:ℕ)) : Finset ℕ),((1:ℝ)-1/((k:ℝ)+2)))=eulerWeight S := by
    rw [Finset.prod_image (fun p hp q hq he => by have := (hS p hp).1; have := (hS q hq).1; omega)]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [primeFactor]
    rw [Nat.cast_sub (hS p hp).1]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [himage,shifted_product] at hprod
  exact (one_div_le_one_div_of_le (by positivity) hnP).trans hprod

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve


lemma primeFactor_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ primeFactor p := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p:ℝ)-1 := by linarith
  have hh := (div_le_one hden).mpr (show (1:ℝ) ≤ (p:ℝ)-1 by linarith)
  unfold primeFactor
  linarith

lemma eulerWeight_nonneg (S : Finset ℕ) (hS : ∀ p∈S,2 ≤ p) : 0 ≤ eulerWeight S :=
  Finset.prod_nonneg (fun p hp => primeFactor_nonneg p (hS p hp))

lemma eulerWeight_eq_zero_of_two (S : Finset ℕ) (hS : 2∈S) : eulerWeight S=0 := by
  apply Finset.prod_eq_zero hS
  norm_num [primeFactor]

lemma odd_of_eulerWeight_ne_zero (S : Finset ℕ) (hS : ∀ p∈S,2 ≤ p)
    (hne : eulerWeight S≠0) : ∀ p∈S,3 ≤ p := by
  intro p hp
  have hp2 := hS p hp
  by_contra h
  have he : p=2 := by omega
  subst p
  exact hne (eulerWeight_eq_zero_of_two S hp)





open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
open NumberTheoryLean
attribute [local instance] Classical.propDecidable

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology BigOperators
open Erdos970Dependency.SiegelWalfisz ErdosUnitLifts

theorem unit_lift_sieve_lower_eventually (Cs K xi gamma : ℝ)
    (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hxi : 0 < xi) (hgamma : 0 < gamma) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R V : ℝ,3 ≤ P → P ≤ Real.exp (K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A B : ℤ,∀ residue : ℕ → ℤ,
      IsUnit (A:ZMod D) → IsUnit (B:ZMod D) → ∀ S : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈S,t.Prime) → (∀ t∈S,(t:ℝ) ≤ P) → (∀ t∈S,¬t∣D) → (∀ t∈S,rho t≠0) →
      (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*eulerWeight S ≤
        ((survivorPrimes R V (D*radical D) S (actualClasses D A B residue) rho).card:ℝ) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hSieve⟩ := finite_tag_sieve_error_jb247
  let s : ℝ := max 480024 (-96*Real.log (gamma/2))
  have hs : 480024 ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hrel : Real.exp (-s/96) ≤ gamma/2 := by
    have hh := le_max_right (480024:ℝ) (-96*Real.log (gamma/2))
    change -96*Real.log (gamma/2) ≤ s at hh
    calc
      _ ≤ Real.exp (Real.log (gamma/2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by positivity)
  obtain ⟨Wn,_hWn,hNlower⟩ := moving_subbin_prime_lower Cs xi hCs hxi
  have hMod := eventually_moving_exponential_domination (2*Cs) s K c (by linarith) hs0 hK hc
  have hRate := eventually_moving_error (4*Cs+10) (s+1) K c (64*C/xi) (gamma/2)
    (by linarith) (by linarith) hK hc (by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop (max Wn X₀),hMod,hRate] with w hw hwMod hwRate
  refine ⟨hwMod.1,?_⟩
  intro P R V hP hPcap hRscale hlo hhi D hD hDw A B residue hAunit hBunit S rho hPrime hsize hSD hrho
  let Q := D*radical D
  let Cls := actualClasses D A B residue
  let N : ℝ := (intervalPrimes R V 1 0).card
  have hw3 := hwMod.1
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hD0 : (0:ℝ) < D := by exact_mod_cast hD
  have hQ : 0 < Q := Nat.mul_pos hD (radical_pos D)
  obtain ⟨hR0,hV0,hVR,hN,hN0⟩ := hNlower w R V ((le_max_left _ _).trans hw) hRscale hlo hhi
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith)).trans hRscale
  have hRX : X₀ ≤ R := ((le_max_right _ _).trans hw).trans hRw
  have hR3 : 3 ≤ R := hw3.trans hRw
  have hL : 0 < Real.log R := Real.log_pos (by linarith)
  have hWnonneg : 0 ≤ eulerWeight S := eulerWeight_nonneg S (fun t ht => (hPrime t ht).two_le)
  by_cases hzero : eulerWeight S=0
  · rw [hzero,mul_zero]
    exact Nat.cast_nonneg _
  have hOdd : ∀ t∈S,3 ≤ t := odd_of_eulerWeight_ne_zero S (fun t ht => (hPrime t ht).two_le) hzero
  have hEW : 1/P ≤ eulerWeight S := eulerWeight_lower P hP S (fun t ht => ⟨hOdd t ht,hsize t ht⟩)
  have hQS : ∀ t∈S,Q.Coprime t := by
    intro t ht
    have hdt := ((hPrime t ht).coprime_iff_not_dvd.mpr (hSD t ht)).symm
    exact Nat.coprime_mul_iff_left.mpr ⟨hdt,Nat.Coprime.coprime_dvd_left (radical_dvd D) hdt⟩
  have hCls : ∀ a∈Cls,a<Q ∧ a.Coprime Q := fun a ha =>
    actualClasses_reduced D hD A B residue hAunit hBunit a ha
  have hlevel : (Q:ℝ)*P^s ≤ Real.exp (c*cubeHeight R) :=
    (mul_le_mul_of_nonneg_right (lift_modulus_bound hw0 hD hDw) (Real.rpow_nonneg hP0.le s)).trans
      (hwMod.2 P R (by linarith) hPcap hRscale)
  have hf := hSieve R V hRX hV0.le hVR Q hQ S Cls rho hPrime hOdd hQS
    (fun a ha => (hCls a ha).1) (fun a ha => (hCls a ha).2) hrho P s hP hs hsize hlevel
  have hXeq : N*(Cls.card:ℝ)/(Q.totient:ℝ)=N/(D:ℝ) := by
    calc
      _ = N*((Cls.card:ℝ)/(Q.totient:ℝ)) := by ring
      _ = N*(1/(D:ℝ)) := by rw [actualClasses_fraction_real D hD A B residue hBunit]
      _ = _ := by ring
  dsimp only at hf
  change |((survivorPrimes R V Q S Cls rho).card:ℝ)-(N*(Cls.card:ℝ)/(Q.totient:ℝ))*eulerWeight S| ≤ _ at hf
  rw [hXeq] at hf
  have hNV : xi*R/(64*w^(2*Cs+10)*Real.log R) ≤ N := by
    have hv := (le_div_iff₀ hR0).mp hlo
    have hh := div_le_div_of_nonneg_right hv (show 0 ≤ 4*Real.log R by positivity)
    have he : ((xi/(16*w^(2*Cs+10)))*R)/(4*Real.log R)=xi*R/(64*w^(2*Cs+10)*Real.log R) := by ring
    rw [he] at hh
    exact hh.trans hN
  have hCard : (Cls.card:ℝ) ≤ D := by exact_mod_cast actualClasses_card_le D hD A B residue hBunit
  have hrem := relative_remainder_bound (Cls.card:ℝ) (D:ℝ) (w^Cs) N (eulerWeight S)
    (w^(2*Cs+10)) P (Real.log R) R C (P^s) (Real.exp (-c*cubeHeight R)) xi
    (Nat.cast_nonneg _) hCard hD0 hDw (by positivity) hP0 hL hR0 hC.le
    (Real.rpow_nonneg hP0.le s) (Real.exp_pos _).le hxi hNV hEW
  have hwPower : (w^Cs)^2*w^(2*Cs+10)=w^(4*Cs+10) := by
    rw [← Real.rpow_mul_natCast hw0.le,← Real.rpow_add hw0]
    congr 1
    norm_num
    ring
  have hPPower : P*(P^s)=P^(s+1) := by rw [Real.rpow_add_one hP0.ne']; ring
  have hshape : (64*C/xi)*(w^Cs)^2*w^(2*Cs+10)*P*(P^s)*Real.log R*Real.exp (-c*cubeHeight R)=
      (64*C/xi)*w^(4*Cs+10)*P^(s+1)*Real.log R*Real.exp (-c*cubeHeight R) := by
    calc
      _ = (64*C/xi)*((w^Cs)^2*w^(2*Cs+10))*(P*(P^s))*Real.log R*Real.exp (-c*cubeHeight R) := by ring
      _ = _ := by rw [hwPower,hPPower]
  rw [hshape] at hrem
  have hr := hwRate.2 P R (by linarith) hPcap hRscale
  have hmu : 0 ≤ (N/(D:ℝ))*eulerWeight S := mul_nonneg (div_nonneg hN0.le hD0.le) hWnonneg
  have hrem' := hrem.trans (mul_le_mul_of_nonneg_left hr hmu)
  have hrel' := mul_le_mul_of_nonneg_left hrel hmu
  have hAbs := hf.trans (add_le_add hrel' hrem')
  have hLower := (abs_le.mp hAbs).1
  change (1-gamma)*(N/(D:ℝ))*eulerWeight S ≤ ((survivorPrimes R V Q S Cls rho).card:ℝ)
  nlinarith

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagAffineConditions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

lemma actual_bad_iff (D t : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (p : ℕ)
    (ht : t.Prime) (htD : ¬t∣D) (hint : (D:ℤ)∣A+B*p) :
    (actualN D A B p:ZMod t)=residue t ↔
      (B:ZMod t)*(p:ZMod t)=(D:ZMod t)*(residue t)-A := by
  have hn : (D:ℤ)*actualN D A B p=A+B*p := by
    unfold actualN
    rw [mul_comm]
    exact Int.ediv_mul_cancel hint
  have hh := congrArg (fun z : ℤ => (z:ZMod t)) hn
  simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast] at hh
  have hu : IsUnit (D:ZMod t) := (ZMod.isUnit_iff_coprime _ _).mpr
    (ht.coprime_iff_not_dvd.mpr htD).symm
  constructor
  · intro he
    rw [he] at hh
    linear_combination -hh
  · intro he
    apply hu.mul_left_cancel
    rw [hh,he]
    ring

lemma mul_forbidden_iff (D t : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (p : ℕ)
    (hB : IsUnit (B:ZMod t)) :
    (B:ZMod t)*(p:ZMod t)=(D:ZMod t)*(residue t)-A ↔
      (p:ZMod t)=forbiddenClass D A B residue t := by
  have hh := affine_eq_iff t 0 B ((D:ℤ)*(residue t)-A) hB (p:ZMod t)
  simpa only [Int.cast_zero,zero_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,sub_zero,forbiddenClass] using hh

lemma prime_cast_ne_zero_of_large (P : ℝ) (p t : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ))
    (ht : t∈smallPrimeSet P) : (p:ZMod t)≠0 := by
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp ht
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff p t).mp hz
  rcases hp.eq_one_or_self_of_dvd t hd with he | he
  · exact htp.ne_one he
  · have her : (t:ℝ)=p := by exact_mod_cast he
    linarith

theorem all_small_avoidance_iff (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (p : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ)) (hint : (D:ℤ)∣A+B*p) :
    (∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t) ↔
      (∀ t∈D.primeFactors,(actualN D A B p:ZMod t)≠residue t) ∧
      (∀ t∈restrictedPrimes P D A residue d0,(p:ZMod t)≠forbiddenClass D A B residue t) := by
  constructor
  · intro h
    constructor
    · intro t ht
      have htP : (t:ℝ)<P := (show (t:ℝ) ≤ D by exact_mod_cast Nat.le_of_dvd hD (Nat.dvd_of_mem_primeFactors ht)).trans_lt hDP
      exact h t ((mem_smallPrimeSet P t).mpr ⟨Nat.prime_of_mem_primeFactors ht,htP⟩)
    · intro t ht he
      have htE := (Finset.mem_filter.mp ht).1
      obtain ⟨htS,htD,_⟩ := Finset.mem_filter.mp htE
      have htP := ((mem_smallPrimeSet P t).mp htS).1
      have hBunit := restricted_coefficient_unit P D A B residue d0 hprofile t ht
      exact h t htS ((actual_bad_iff D t A B residue p htP htD hint).mpr
        ((mul_forbidden_iff D t A B residue p hBunit).mpr he))
  · rintro ⟨hDen,hRest⟩ t htS hbad
    have htp := ((mem_smallPrimeSet P t).mp htS).1
    by_cases htD : t∣D
    · exact hDen t (Nat.mem_primeFactors.mpr ⟨htp,htD,hD.ne'⟩) hbad
    have hmul := (actual_bad_iff D t A B residue p htp htD hint).mp hbad
    by_cases hrhs : (D:ZMod t)*(residue t)-A=0
    · have hnot : ¬t∣d0 := by
        intro hd
        have hE := hsupport t (Nat.mem_primeFactors.mpr ⟨htp,hd,hd0.ne'⟩)
        exact (Finset.mem_filter.mp hE).2.2 hrhs
      have hBunit := coefficient_unit_of_not_dvd htp B (hprofile t htS) hnot
      let _ : Fact t.Prime := ⟨htp⟩
      have hp0 := prime_cast_ne_zero_of_large P p t hp hPp htS
      have hB0 : (B:ZMod t)≠0 := isUnit_iff_ne_zero.mp hBunit
      rw [hrhs] at hmul
      exact mul_ne_zero hB0 hp0 hmul
    · have htE : t∈unalignedPrimes P D A residue := Finset.mem_filter.mpr ⟨htS,htD,hrhs⟩
      by_cases htd : t∣d0
      · have hB0 := coefficient_cast_zero (hprofile t htS) htd
        rw [hB0,zero_mul] at hmul
        exact hrhs hmul.symm
      · have htR : t∈restrictedPrimes P D A residue d0 := Finset.mem_filter.mpr ⟨htE,htd⟩
        have hBunit := restricted_coefficient_unit P D A B residue d0 hprofile t htR
        exact hRest t htR ((mul_forbidden_iff D t A B residue p hBunit).mp hmul)

theorem local_survivor_conditions (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (p : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ)) :
    ((D:ℤ)∣A+B*p ∧ ∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t) ↔
      (p%(D*radical D)∈actualClasses D A B residue ∧
        ∀ t∈restrictedPrimes P D A residue d0,(p:ZMod t)≠forbiddenClass D A B residue t) := by
  rw [mem_actualClasses_mod_iff D hD A B residue p]
  constructor
  · rintro ⟨hint,h⟩
    have hh := (all_small_avoidance_iff P D hD hDP A B residue d0 hd0 hsupport hprofile p hp hPp hint).mp h
    exact ⟨⟨hint,hh.1⟩,hh.2⟩
  · rintro ⟨⟨hint,hDen⟩,hRest⟩
    exact ⟨hint,(all_small_avoidance_iff P D hD hDP A B residue d0 hd0 hsupport hprofile p hp hPp hint).mpr ⟨hDen,hRest⟩⟩

theorem actualSurvivorPrimes_eq_sieve (P R V : ℝ) (hPR : P ≤ R)
    (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P) (A B : ℤ) (residue : ℕ → ℤ)
    (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0) :
    actualSurvivorPrimes P R V D A B residue=
      survivorPrimes R V (D*radical D) (restrictedPrimes P D A residue d0)
        (actualClasses D A B residue) (forbiddenClass D A B residue) := by
  ext p
  simp only [actualSurvivorPrimes,survivorPrimes,basePrimes,Finset.mem_filter]
  by_cases hp : p∈intervalPrimes R V 1 0
  · simp only [hp,true_and]
    have h := (mem_intervalPrimes R V 1 0 p).mp hp
    exact local_survivor_conditions P D hD hDP A B residue d0 hd0 hsupport hprofile p h.1 (hPR.trans h.2.1.le)
  · simp only [hp,false_and]

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_TagPrimeSieveLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology
open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz

theorem tag_prime_sieve_lower_jb247_oai (Cs K rho xi gamma : ℝ)
    (hCs : 0 ≤ Cs) (hK : 0 < K) (hrho : 1 < rho) (hxi : 0 < xi) (hgamma : 0 < gamma) :
    ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w P R V : ℝ,w₀ ≤ w →
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp ((rho*K)*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A : ℤ,A.natAbs.Coprime D →
      ∀ residue : ℕ → ℤ,∀ q d0 ell : ℕ,∀ m : ℤ,
      (∀ t∈smallPrimeSet P,q.Coprime t) → 0 < d0 →
      (∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue) →
      ell.Prime → P<(ell:ℝ) → m.natAbs=d0*ell →
      (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*
        eulerWeight (restrictedPrimes P D A residue d0) ≤
        ((actualSurvivorPrimes P R V D A ((q:ℤ)*m) residue).card:ℝ) := by
  have hcap : 0 ≤ rho*K := mul_nonneg (by linarith) hK.le
  obtain ⟨WC,hWC⟩ := eventually_atTop.mp
    (unit_lift_sieve_lower_eventually Cs (rho*K) xi gamma hCs hcap hxi hgamma)
  obtain ⟨WD,hWD⟩ := eventually_atTop.mp (eventually_cutoff_dominates (max Cs 1) K hK)
  obtain ⟨WT,hWT⟩ := eventually_atTop.mp (eventually_cutoff_le_subbin (rho*K))
  refine ⟨max 3 (max WC (max WD WT)),le_max_left _ _,?_⟩
  intro w P R V hw hPlow hPup hR hlo hhi D hD hDw A hAc residue q d0 ell m hq hd0 hsupport hell hellP hm
  have hwAll : max WC (max WD WT) ≤ w := (le_max_right _ _).trans hw
  have hCore := hWC w ((le_max_left _ _).trans hwAll)
  have hwDt : max WD WT ≤ w := (le_max_right _ _).trans hwAll
  have hDom := hWD w ((le_max_left _ _).trans hwDt)
  have hTag := hWT w ((le_max_right _ _).trans hwDt)
  have hw3 := hCore.1
  have hw1 : 1 ≤ w := by linarith
  have hPow : w ≤ w^(max Cs 1) := Real.self_le_rpow_of_one_le hw1 (le_max_right _ _)
  have hwP : w<P := hPow.trans_lt (hDom.2.trans_le hPlow)
  have hP3 : 3 ≤ P := by linarith
  have hDpow : w^Cs ≤ w^(max Cs 1) := Real.rpow_le_rpow_of_exponent_le hw1 (le_max_left _ _)
  have hDP : (D:ℝ)<P := (hDw.trans hDpow).trans_lt (hDom.2.trans_le hPlow)
  have hPR : P ≤ R := hTag.2 P R hPup hR
  let B : ℤ := (q:ℤ)*m
  have hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0 :=
    signed_coefficient_profile P q d0 ell m hq hell hellP hm
  have hBc : B.natAbs.Coprime D := denominator_coefficient_coprime P D hD hDP A B residue d0 hd0 hsupport hprofile
  have hAu : IsUnit (A:ZMod D) := intCast_isUnit_of_natAbs_coprime D A hAc
  have hBu : IsUnit (B:ZMod D) := intCast_isUnit_of_natAbs_coprime D B hBc
  let S := restrictedPrimes P D A residue d0
  let bad := forbiddenClass D A B residue
  have hInfo : ∀ t∈S,t.Prime ∧ (t:ℝ) ≤ P ∧ ¬t∣D := by
    intro t ht
    have he := (Finset.mem_filter.mp ht).1
    obtain ⟨htS,htD,_⟩ := Finset.mem_filter.mp he
    have hh := (mem_smallPrimeSet P t).mp htS
    exact ⟨hh.1,hh.2.le,htD⟩
  have hCount := hCore.2 P R V hP3 hPup hR hlo hhi D hD hDw A B residue hAu hBu S bad
    (fun t ht => (hInfo t ht).1) (fun t ht => (hInfo t ht).2.1)
    (fun t ht => (hInfo t ht).2.2)
    (fun t ht => forbiddenClass_ne_zero P D A B residue d0 hprofile t ht)
  have hEq := actualSurvivorPrimes_eq_sieve P R V hPR D hD hDP A B residue d0 hd0 hsupport hprofile
  rw [← hEq] at hCount
  exact hCount

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247_oai := @OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247_oai
