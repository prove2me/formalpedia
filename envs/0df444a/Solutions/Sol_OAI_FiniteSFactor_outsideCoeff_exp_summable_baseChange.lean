-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideCoeff_exp_summable_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:43:09.733384+00:00
-- url     : https://prove2.me/submissions/18378f7c-0bf6-4ea1-89b9-400c66042c36

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_norm_le_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
namespace FiniteSFactor
private theorem fiber_card_natCard (n : ℕ) :
    (fiber n).card = Nat.card {I : Ideal O // Ideal.absNorm I = n} := by
  change (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset.card =
    Set.ncard {I : Ideal O | Ideal.absNorm I = n}
  exact (Set.ncard_eq_toFinset_card _ _).symm
private theorem fiber_card_le_count (n : ℕ) :
    (fiber n).card ≤ Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} := by
  let f : {I : Ideal O // Ideal.absNorm I = n} →
      {I : Ideal O // Ideal.absNorm I ≤ n} :=
    fun I => ⟨I.1, I.2.le⟩
  have hinj : Function.Injective f := by
    intro I J h
    have hval : I.1 = J.1 :=
      congrArg (fun x : {I : Ideal O // Ideal.absNorm I ≤ n} => x.1) h
    exact Subtype.ext hval
  have hfin : Finite {I : Ideal O // Ideal.absNorm I ≤ n} :=
    Ideal.finite_setOfPred_absNorm_le n
  simpa only [fiber_card_natCard] using Nat.card_le_card_of_injective f hinj
private theorem count_isBigO :
    (fun n : ℕ =>
      (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hlim :=
    (NumberField.Ideal.tendsto_norm_le_div_atTop (CyclotomicField 3 ℚ)).comp
      tendsto_natCast_atTop_atTop
  have hlim' : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) / (n : ℝ))
      atTop (nhds ((2 ^ NumberField.InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) *
        NumberField.Units.regulator (CyclotomicField 3 ℚ) *
        (NumberField.classNumber (CyclotomicField 3 ℚ) : ℝ)) /
        ((NumberField.Units.torsionOrder (CyclotomicField 3 ℚ) : ℝ) *
          Real.sqrt |(NumberField.discr (CyclotomicField 3 ℚ) : ℝ)|))) := by
    simpa [Function.comp_def] using hlim
  have hzero : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) = 0 →
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hz
    have hn0 : n = 0 := by exact_mod_cast hz
    exact (Nat.ne_of_gt hn hn0).elim
  exact Asymptotics.isBigO_of_div_tendsto_nhds hzero _ hlim'
private theorem fiber_card_eventually_le_linear :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ((fiber n).card : ℝ) ≤ C * n := by
  obtain ⟨C, hC⟩ := count_isBigO.bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  calc
    ((fiber n).card : ℝ) ≤
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) := by
          exact_mod_cast fiber_card_le_count n
    _ = ‖(Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)‖ := by simp
    _ ≤ C * ‖(n : ℝ)‖ := hn
    _ = C * n := by simp
private theorem outsideCoeff_norm_le_card (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hw : ∀ I, ‖w I‖ ≤ 1) (n : ℕ) :
    ‖outsideCoeff S w n‖ ≤ ((fiber n).card : ℝ) := by
  classical
  have hweight (I : Ideal O) : ‖outsideWeight S w I‖ ≤ 1 := by
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [if_pos hgood]
      exact hw I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [if_neg hgood]
      simp
  unfold outsideCoeff
  calc
    ‖∑ I ∈ fiber n, outsideWeight S w I‖ ≤
        ∑ I ∈ fiber n, ‖outsideWeight S w I‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ fiber n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hweight I
    _ = ((fiber n).card : ℝ) := by simp
private theorem baseChangeWeight_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖ShortDraftHeckeBridge.baseChangeWeight χ I‖ ≤ 1 := by
  have hμ : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
    by_cases hsq : Squarefree I
    · simp [hsq.moebius_eq]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hχ : ‖χ (Ideal.absNorm I)‖ ≤ 1 := χ.norm_le_one _
  rw [ShortDraftHeckeBridge.baseChangeWeight, norm_mul]
  calc
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ * ‖χ (Ideal.absNorm I)‖ ≤
        1 * ‖χ (Ideal.absNorm I)‖ :=
      mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ ≤ 1 := by simpa using hχ
end FiniteSFactor
open Filter
namespace CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
end CompactScaleBridge
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) n * Real.exp (-(n : ℝ) * t)) := by
  obtain ⟨C, hC⟩ := fiber_card_eventually_le_linear
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * t)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 ht using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  apply (hexp.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hC] with n hn
  have hcoeff := outsideCoeff_norm_le_card S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (baseChangeWeight_norm_le_one χ) n
  have hlin : ‖outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n‖ ≤
      C * (n : ℝ) := hcoeff.trans hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(n : ℝ) * t)).le)
end OAI.FiniteSFactor
