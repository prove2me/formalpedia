-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:25:55.613269+00:00
-- url     : https://prove2.me/submissions/afbf9548-e140-4ae5-b337-bbef4b39a154

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uX
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (F : α → X → ℝ) (hF : ∀ i, Measurable (F i))
    (hm : ν=∑ i, ENNReal.ofReal (p i) • μ.map (F i))
    (f : ℝ → ℤ) (hf : Measurable f) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f (F i y) ∈ s) :
    (∫ y, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) ∂μ) ≤ entropy ν f := by
  set m : ℤ → X → ℝ := fun b y => ∑ a, if f (F a y) = b then p a else 0 with hm_def
  have hmass_eq : ∀ y b, FiniteEntropy.mass Finset.univ p (fun i => f (F i y)) b = m b y := by
    intro y b
    simp only [FiniteEntropy.mass, hm_def, Finset.sum_filter]
  have hpre : ∀ a b, MeasurableSet ((f ∘ F a) ⁻¹' {b}) :=
    fun a b => (hf.comp (hF a)) (measurableSet_singleton b)
  have hterm : ∀ a b, (fun y => if f (F a y) = b then p a else 0) =
      Set.indicator ((f ∘ F a) ⁻¹' {b}) (fun _ => p a) := by
    intro a b
    funext y
    by_cases h : f (F a y) = b
    · rw [if_pos h, Set.indicator_of_mem (show y ∈ (f ∘ F a) ⁻¹' {b} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (f ∘ F a) ⁻¹' {b} from h)]
  have hmeas_m : ∀ b, Measurable (m b) := by
    intro b
    simp only [hm_def]
    refine Finset.measurable_sum _ (fun a _ => ?_)
    rw [hterm a b]
    exact measurable_const.indicator (hpre a b)
  have hm01 : ∀ b y, 0 ≤ m b y ∧ m b y ≤ 1 := by
    intro b y
    simp only [hm_def]
    refine ⟨Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [hp a]), ?_⟩
    rw [← hp1]
    exact Finset.sum_le_sum (fun a _ => by split_ifs <;> simp [hp a])
  have hint_m : ∀ b, Integrable (m b) μ := fun b =>
    Integrable.of_bound (hmeas_m b).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm01 b y).1]; exact (hm01 b y).2)
  have hint_nm : ∀ b, Integrable (fun y => Real.negMulLog (m b y)) μ := fun b =>
    Integrable.of_bound ((Real.continuous_negMulLog.measurable.comp (hmeas_m b)).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg (hm01 b y).1 (hm01 b y).2)]
        linarith [Real.negMulLog_le_one_sub_self (hm01 b y).1, (hm01 b y).1])
  have hmassν : ∀ b, mass ν f b = ∑ a, p a * μ.real ((f ∘ F a) ⁻¹' {b}) := by
    intro b
    unfold mass
    rw [measureReal_def, hm, Measure.coe_finset_sum, Finset.sum_apply,
      ENNReal.toReal_sum (fun a _ => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (hF a) (show MeasurableSet {x | f x = b} from hf (measurableSet_singleton b)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp a), measureReal_def]
    rfl
  have hint_eq : ∀ b, ∫ y, m b y ∂μ = mass ν f b := by
    intro b
    rw [hmassν]
    simp only [hm_def]
    rw [integral_finset_sum _ (fun a _ => by
      rw [hterm a b]; exact (integrable_const _).indicator (hpre a b))]
    apply Finset.sum_congr rfl
    intro a _
    rw [hterm a b, integral_indicator_const _ (hpre a b), smul_eq_mul, mul_comm]
  have hG : ∀ᵐ y ∂μ, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) =
      ∑ b ∈ s, Real.negMulLog (m b y) := by
    filter_upwards [ae_all_iff.2 hs] with y hy
    unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
    have hsub : Finset.univ.image (fun i => f (F i y)) ⊆ s := by
      intro b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      exact hy i
    rw [Finset.sum_subset hsub (fun b _ hb => by
      rw [FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ hb, Real.negMulLog_zero])]
    apply Finset.sum_congr rfl
    intro b _
    rw [hmass_eq]
  have hνs : ∀ b ∉ s, mass ν f b = 0 := by
    intro b hb
    rw [hmassν]
    apply Finset.sum_eq_zero
    intro a _
    have h0 : μ ((f ∘ F a) ⁻¹' {b}) = 0 := by
      apply measure_mono_null _ (ae_iff.mp (hs a))
      intro y hy
      simp only [Set.mem_preimage, Function.comp, Set.mem_singleton_iff] at hy
      simp only [Set.mem_setOf_eq, hy]
      exact hb
    rw [measureReal_def, h0]
    simp
  have hent : entropy ν f = ∑ b ∈ s, Real.negMulLog (mass ν f b) := by
    unfold entropy
    exact tsum_eq_sum (fun b hb => by rw [hνs b hb, Real.negMulLog_zero])
  rw [integral_congr_ae hG, integral_finset_sum _ (fun b _ => hint_nm b), hent]
  apply Finset.sum_le_sum
  intro b _
  rw [← hint_eq b]
  exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun y => (hm01 b y).1) (hint_m b) (hint_nm b)

