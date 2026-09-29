-- Prove2me | solution 1 for MarkovChainCLT.clt_of_bounded_of_summable_alpha
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:18:15.261506+00:00
-- url     : https://prove2.me/submissions/e0953226-13ce-43d8-8d39-e1b2287272d3

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_bounded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NumberBoundedAlphaPort_LayerCake_bounded_layercake_identity

open MeasureTheory Set
open scoped Topology ENNReal

theorem solution (u M : ℝ) (h : |u| ≤ M) :
    u + M = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio u) 1 t := by
  have hlo : -M ≤ u := by
    have := neg_le_of_abs_le h
    linarith
  have hhi : u ≤ M := le_of_abs_le h
  have hset : Set.Icc (-M) M ∩ Set.Iio u = Set.Ico (-M) u := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2.le hhi⟩, h2⟩
  have hint : ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio u) 1 t
      = ∫ _ in Set.Ico (-M) u, (1 : ℝ) := by
    rw [setIntegral_indicator (measurableSet_Iio (a := u)), hset]
    rfl
  rw [hint]
  have hvol : ((volume.restrict (Set.Ico (-M) u)) Set.univ).toReal = u + M := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ u - -M)]
    ring
  have hint2 : (∫ _ in Set.Ico (-M) u, (1 : ℝ))
      = ((volume.restrict (Set.Ico (-M) u)) Set.univ).toReal := by
    simp [integral_const, smul_eq_mul, Measure.real_def]
  rw [hint2, hvol]

end NumberBoundedAlphaPort_LayerCake_bounded_layercake_identity


namespace NumberBoundedAlphaPort_LayerCake_expectation_add_const

open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (hWm : Measurable W) (M : ℝ) (hWb : ∀ ω, |W ω| ≤ M) :
    ∫ ω, (W ω + M) ∂P
      = ∫ t in Set.Icc (-M) M, (P {ω | W ω > t}).toReal := by
  have hS_meas : MeasurableSet {(p : Ω × ℝ) | W p.1 > p.2} :=
    measurableSet_lt measurable_snd (hWm.comp measurable_fst)
  have hF_meas : Measurable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2) := by
    have heq : (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | W p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : W p.1 > p.2
      · have hm : p.2 ∈ Set.Iio (W p.1) := Set.mem_Iio.2 h
        have h2 : p ∈ {(p : Ω × ℝ) | W p.1 > p.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : p.2 ∉ Set.Iio (W p.1) := by
          simpa [Set.mem_Iio] using h
        have h2 : p ∉ {(p : Ω × ℝ) | W p.1 > p.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq]
    exact Measurable.indicator measurable_const hS_meas
  have hIcc_fin : volume (Set.Icc (-M) M) < ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI : Fact (volume (Set.Icc (-M) M) < ∞) := ⟨hIcc_fin⟩
  have hF_bdd : ∀ᵐ p : Ω × ℝ ∂(P.prod (volume.restrict (Set.Icc (-M) M))),
      ‖Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2‖ ≤ 1 := by
    filter_upwards with p
    by_cases h : W p.1 > p.2
    · have hm : p.2 ∈ Set.Iio (W p.1) := Set.mem_Iio.2 h
      rw [Set.indicator_of_mem hm]
      simp
    · have hm : p.2 ∉ Set.Iio (W p.1) := by
        simpa [Set.mem_Iio] using h
      rw [Set.indicator_of_notMem hm]
      simp
  have hF_int : Integrable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2)
      (P.prod (volume.restrict (Set.Icc (-M) M))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable 1 hF_bdd
  have hW_eq : ∀ ω : Ω, W ω + M
      = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio (W ω)) 1 t :=
    fun ω => _root_.NumberBoundedAlphaPort_LayerCake_bounded_layercake_identity.solution (W ω) M (hWb ω)
  have hAt_amb : ∀ t : ℝ, MeasurableSet {ω | W ω > t} :=
    fun t => hWm measurableSet_Ioi
  have hF_unc : Integrable
      (Function.uncurry fun ω t => Set.indicator (Set.Iio (W ω)) (1 : ℝ → ℝ) t)
      (P.prod (volume.restrict (Set.Icc (-M) M))) := hF_int
  have hswap := integral_integral_swap hF_unc
  have hLHS : (∫ ω, ∫ t, Set.indicator (Set.Iio (W ω)) 1 t
      ∂(volume.restrict (Set.Icc (-M) M)) ∂P)
      = ∫ ω, (W ω + M) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    exact (hW_eq ω).symm
  have hRHS : (∫ t, ∫ ω, Set.indicator (Set.Iio (W ω)) 1 t ∂P
      ∂(volume.restrict (Set.Icc (-M) M)))
      = ∫ t in Set.Icc (-M) M, (P {ω | W ω > t}).toReal := by
    apply integral_congr_ae
    filter_upwards with t
    have heq : (fun ω => Set.indicator (Set.Iio (W ω)) 1 t)
        = Set.indicator {ω | W ω > t} (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : W ω > t
      · have hm : t ∈ Set.Iio (W ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | W ω > t} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : t ∉ Set.Iio (W ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | W ω > t} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq, integral_indicator_const _ (hAt_amb t)]
    simp [Measure.real_def]
  rw [← hLHS, hswap]
  exact hRHS

end NumberBoundedAlphaPort_LayerCake_expectation_add_const


namespace NumberBoundedAlphaPort_ProbabilityTheory_cov_indicator_eq

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[Set.indicator A (fun _ => (1 : ℝ)), Set.indicator B (fun _ => (1 : ℝ)); P]
      = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal := by
  have hbdA : ∀ᵐ ω ∂P, ‖Set.indicator A (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simp
  have h1A : MemLp (Set.indicator A (fun _ => (1 : ℝ))) 2 P :=
    MemLp.of_bound ((measurable_const).indicator hA).aestronglyMeasurable 1 hbdA
  have hbdB : ∀ᵐ ω ∂P, ‖Set.indicator B (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simp
  have h1B : MemLp (Set.indicator B (fun _ => (1 : ℝ))) 2 P :=
    MemLp.of_bound ((measurable_const).indicator hB).aestronglyMeasurable 1 hbdB
  rw [covariance_eq_sub h1A h1B]
  have eA : P[Set.indicator A (fun _ => (1 : ℝ))] = (P A).toReal := by
    rw [integral_indicator_const _ hA]
    simp [Measure.real_def]
  have eB : P[Set.indicator B (fun _ => (1 : ℝ))] = (P B).toReal := by
    rw [integral_indicator_const _ hB]
    simp [Measure.real_def]
  have eAB : P[Set.indicator A (fun _ => (1 : ℝ)) * Set.indicator B (fun _ => (1 : ℝ))]
      = (P (A ∩ B)).toReal := by
    have hmul : (Set.indicator A (fun _ => (1 : ℝ)) * Set.indicator B (fun _ => (1 : ℝ)))
        = Set.indicator (A ∩ B) (fun _ => (1 : ℝ)) := by
      funext ω
      simp only [Pi.mul_apply]
      by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
    rw [hmul, integral_indicator_const _ (hA.inter hB)]
    simp [Measure.real_def]
  rw [eA, eB, eAB]

end NumberBoundedAlphaPort_ProbabilityTheory_cov_indicator_eq


namespace NumberBoundedAlphaPort_MarkovChainCLT_processSigma_le_of_measurable

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : ℕ → Ω → E) (hY : ∀ n, Measurable (Y n)) (s : Set ℕ) :
    processSigma Y s ≤ ‹MeasurableSpace Ω› := by
  unfold processSigma
  apply iSup₂_le
  intro i _
  exact measurable_iff_comap_le.1 (hY i)

end NumberBoundedAlphaPort_MarkovChainCLT_processSigma_le_of_measurable


namespace NumberBoundedAlphaPort_MarkovChainCLT_alpha_indicator_cov_le

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ)
    (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ alphaMixingCoef P Y n := by
  have hmem : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ∈
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal - (P A').toReal * (P B').toReal|} :=
    ⟨k, A, B, hA, hB, rfl⟩
  have hbdd : BddAbove
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal - (P A').toReal * (P B').toReal|} := by
    use 1
    intro r hr
    obtain ⟨k', A', B', _, _, rfl⟩ := hr
    have h1 : (P (A' ∩ B')).toReal ≤ 1 := by
      have h : P (A' ∩ B') ≤ 1 := by
        calc P (A' ∩ B') ≤ P Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      exact ENNReal.toReal_mono (by simp) h
    have h2 : (P A').toReal * (P B').toReal ≤ 1 := by
      have hA1 : (P A').toReal ≤ 1 := by
        have h : P A' ≤ 1 := by
          calc P A' ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) h
      have hB1 : (P B').toReal ≤ 1 := by
        have h : P B' ≤ 1 := by
          calc P B' ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) h
      have nnA : 0 ≤ (P A').toReal := ENNReal.toReal_nonneg
      have nnB : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
      calc (P A').toReal * (P B').toReal ≤ 1 * 1 :=
            mul_le_mul hA1 hB1 nnB (by linarith)
        _ = 1 := one_mul 1
    have nn1 : 0 ≤ (P (A' ∩ B')).toReal := ENNReal.toReal_nonneg
    have nn2 : 0 ≤ (P A').toReal * (P B').toReal :=
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  unfold alphaMixingCoef
  exact le_csSup hbdd hmem

end NumberBoundedAlphaPort_MarkovChainCLT_alpha_indicator_cov_le


namespace NumberBoundedAlphaPort_MarkovChainCLT_alpha_cov_bounded

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal Topology

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (M : ℝ) (hM0 : 0 ≤ M) (hUb : ∀ ω, |U ω| ≤ M) (hVb : ∀ ω, |V ω| ≤ M) :
    |cov[U, V; P]| ≤ 4 * M ^ 2 * alphaMixingCoef P Y n := by
  -- Stage 1: past/future sit below ambient; U, V are ambient-measurable and L².
  have hle_past : processSigma Y (Set.Iic k) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberBoundedAlphaPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberBoundedAlphaPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hUm : Measurable U := hU.mono hle_past le_rfl
  have hVm : Measurable V := hV.mono hle_fut le_rfl
  have hU2 : MemLp U 2 P :=
    MemLp.of_bound hUm.aestronglyMeasurable M
      (by filter_upwards with ω using hUb ω)
  have hV2 : MemLp V 2 P :=
    MemLp.of_bound hVm.aestronglyMeasurable M
      (by filter_upwards with ω using hVb ω)
  -- Stage 2: superlevel sets are past/future-measurable; per-(t,s) alpha bound.
  have hAt : ∀ t : ℝ, MeasurableSet[processSigma Y (Set.Iic k)] {ω | U ω > t} :=
    fun t => hU measurableSet_Ioi
  have hBs : ∀ s : ℝ, MeasurableSet[processSigma Y (Set.Ici (k + n))] {ω | V ω > s} :=
    fun s => hV measurableSet_Ioi
  have hα_ts : ∀ t s : ℝ,
      |(P ({ω | U ω > t} ∩ {ω | V ω > s})).toReal
        - (P {ω | U ω > t}).toReal * (P {ω | V ω > s}).toReal|
        ≤ alphaMixingCoef P Y n :=
    fun t s => _root_.NumberBoundedAlphaPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y n k _ _ (hAt t) (hBs s)
  -- Stage 3: joint measurability on the product; layer-cake instances.
  have hS_meas : MeasurableSet {(p : Ω × ℝ) | U p.1 > p.2} :=
    measurableSet_lt measurable_snd (hUm.comp measurable_fst)
  have hT_meas : MeasurableSet {(p : Ω × ℝ) | V p.1 > p.2} :=
    measurableSet_lt measurable_snd (hVm.comp measurable_fst)
  -- Stage 13: V-side joint measurability for the triple integrand.
  have hG_meas : Measurable (fun p : Ω × ℝ => Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2) := by
    have heqG : (fun p : Ω × ℝ => Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | V p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : V p.1 > p.2
      · have hm : p.2 ∈ Set.Iio (V p.1) := Set.mem_Iio.2 h
        have h2 : p ∈ {(p : Ω × ℝ) | V p.1 > p.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : p.2 ∉ Set.Iio (V p.1) := by
          simpa [Set.mem_Iio] using h
        have h2 : p ∉ {(p : Ω × ℝ) | V p.1 > p.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heqG]
    exact Measurable.indicator measurable_const hT_meas
  -- Stage 4: layer-cake integrands on the product; E[U+M] via Fubini.
  -- F(ω,t) = 1_{Uω > t}, jointly measurable, bounded.
  have hF_meas : Measurable (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2) := by
    have heq : (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | U p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : U p.1 > p.2
      · have h2 : p ∈ {(p : Ω × ℝ) | U p.1 > p.2} := h
        have hm : p.2 ∈ Set.Iio (U p.1) := Set.mem_Iio.2 h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have h2 : p ∉ {(p : Ω × ℝ) | U p.1 > p.2} := h
        have hm : p.2 ∉ Set.Iio (U p.1) := by
          simpa [Set.mem_Iio] using h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq]
    exact Measurable.indicator measurable_const hS_meas
  -- Stage 5: finite product measure; Fubini-ready integrability.
  have hIcc_fin : volume (Set.Icc (-M) M) < ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI : Fact (volume (Set.Icc (-M) M) < ∞) := ⟨hIcc_fin⟩
  -- Stage 6: F is integrable on P × (vol restricted to Icc); E[U+M] swap.
  have hF_bdd : ∀ᵐ p : Ω × ℝ ∂(P.prod (volume.restrict (Set.Icc (-M) M))),
      ‖Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2‖ ≤ 1 := by
    filter_upwards with p
    by_cases h : U p.1 > p.2
    · have hm : p.2 ∈ Set.Iio (U p.1) := Set.mem_Iio.2 h
      rw [Set.indicator_of_mem hm]
      simp
    · have hm : p.2 ∉ Set.Iio (U p.1) := by
        simpa [Set.mem_Iio] using h
      rw [Set.indicator_of_notMem hm]
      simp
  have hF_int : Integrable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2)
      (P.prod (volume.restrict (Set.Icc (-M) M))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable 1 hF_bdd
  -- Stage 7: E[U+M] = ∫_{Icc} P(U>t) via pointwise layer-cake + Fubini.
  have hUM_eq : ∀ ω : Ω, U ω + M
      = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio (U ω)) 1 t :=
    fun ω => _root_.NumberBoundedAlphaPort_LayerCake_bounded_layercake_identity.solution (U ω) M (hUb ω)
  -- Stage 8: E[U+M] = ∫_{Icc} P(U>t) by Fubini.
  have hAt_amb : ∀ t : ℝ, MeasurableSet {ω | U ω > t} :=
    fun t => hUm measurableSet_Ioi
  have hBs_amb : ∀ s : ℝ, MeasurableSet {ω | V ω > s} :=
    fun s => hVm measurableSet_Ioi
  have hEU : ∫ ω, (U ω + M) ∂P
      = ∫ t in Set.Icc (-M) M, (P {ω | U ω > t}).toReal := by
    have hF_unc : Integrable
        (Function.uncurry fun ω t => Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t)
        (P.prod (volume.restrict (Set.Icc (-M) M))) := hF_int
    have hswap := integral_integral_swap hF_unc
    -- LHS of swap: ∫ ω, ∫ t in Icc, F = E[U+M] by layer-cake
    have hLHS : (∫ ω, ∫ t, Set.indicator (Set.Iio (U ω)) 1 t
        ∂(volume.restrict (Set.Icc (-M) M)) ∂P)
        = ∫ ω, (U ω + M) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hUM_eq ω).symm
    -- RHS of swap: ∫ t in Icc, ∫ ω, F = ∫ P(A_t)
    have hRHS : (∫ t, ∫ ω, Set.indicator (Set.Iio (U ω)) 1 t ∂P
        ∂(volume.restrict (Set.Icc (-M) M)))
        = ∫ t in Set.Icc (-M) M, (P {ω | U ω > t}).toReal := by
      apply integral_congr_ae
      filter_upwards with t
      have heq : (fun ω => Set.indicator (Set.Iio (U ω)) 1 t)
          = Set.indicator {ω | U ω > t} (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases h : U ω > t
        · have hm : t ∈ Set.Iio (U ω) := Set.mem_Iio.2 h
          have h2 : ω ∈ {ω | U ω > t} := h
          simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
        · have hm : t ∉ Set.Iio (U ω) := by
            simpa [Set.mem_Iio] using h
          have h2 : ω ∉ {ω | U ω > t} := h
          simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
      rw [heq, integral_indicator_const _ (hAt_amb t)]
      simp [Measure.real_def]
    rw [hLHS] at hswap
    rw [hswap]
    exact hRHS
  -- Stage 9: tail-probability map is antitone, hence measurable.
  have hPtail_anti : Antitone (fun t : ℝ => (P {ω | U ω > t}).toReal) := by
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt hab hω
  have hPtail_meas : Measurable (fun t : ℝ => (P {ω | U ω > t}).toReal) :=
    hPtail_anti.measurable
  -- Stage 10: centered per-ω representation.
  have hcenterU : ∀ ω : Ω, (U ω + M) - (∫ ω', (U ω' + M) ∂P)
      = ∫ t in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal) := by
    intro ω
    have hFb : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t‖ ≤ 1 := by
      filter_upwards with t
      by_cases h : t ∈ Set.Iio (U ω)
      · rw [Set.indicator_of_mem h]
        simp
      · rw [Set.indicator_of_notMem h]
        simp
    have hF1 : Integrable (fun t => Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound
        (Measurable.indicator measurable_const measurableSet_Iio).aestronglyMeasurable
        1 hFb
    have hPb : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
      filter_upwards with t
      calc ‖(P {ω | U ω > t}).toReal‖
          = |(P {ω | U ω > t}).toReal| := Real.norm_eq_abs _
        _ ≤ 1 := by
          have hle2 : (P {ω | U ω > t}).toReal ≤ 1 := by
            have hle : P {ω | U ω > t} ≤ 1 := by
              calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_mono (by simp) hle
          have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          exact hle2
    have hP1 : Integrable (fun t => (P {ω | U ω > t}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hPtail_meas.aestronglyMeasurable 1 hPb
    rw [hUM_eq ω, hEU, ← integral_sub hF1 hP1]
  -- Stage 11: V-side expectation + centered representation.
  have hEV : ∫ ω, (V ω + M) ∂P
      = ∫ s in Set.Icc (-M) M, (P {ω | V ω > s}).toReal :=
    _root_.NumberBoundedAlphaPort_LayerCake_expectation_add_const.solution P V hVm M (fun ω => hVb ω)
  have hQtail_anti : Antitone (fun s : ℝ => (P {ω | V ω > s}).toReal) := by
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt hab hω
  have hQtail_meas : Measurable (fun s : ℝ => (P {ω | V ω > s}).toReal) :=
    hQtail_anti.measurable
  have hcenterV : ∀ ω : Ω, (V ω + M) - (∫ ω', (V ω' + M) ∂P)
      = ∫ s in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
    intro ω
    have hGb : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s‖ ≤ 1 := by
      filter_upwards with s
      by_cases h : s ∈ Set.Iio (V ω)
      · rw [Set.indicator_of_mem h]
        simp
      · rw [Set.indicator_of_notMem h]
        simp
    have hG1 : Integrable (fun s => Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound
        (Measurable.indicator measurable_const measurableSet_Iio).aestronglyMeasurable
        1 hGb
    have hQb : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
      filter_upwards with s
      calc ‖(P {ω | V ω > s}).toReal‖
          = |(P {ω | V ω > s}).toReal| := Real.norm_eq_abs _
        _ ≤ 1 := by
          have hle2 : (P {ω | V ω > s}).toReal ≤ 1 := by
            have hle : P {ω | V ω > s} ≤ 1 := by
              calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_mono (by simp) hle
          have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          exact hle2
    have hQ1 : Integrable (fun s => (P {ω | V ω > s}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hQtail_meas.aestronglyMeasurable 1 hQb
    have hVM_eq : V ω + M
        = ∫ s in Set.Icc (-M) M, Set.indicator (Set.Iio (V ω)) 1 s :=
      _root_.NumberBoundedAlphaPort_LayerCake_bounded_layercake_identity.solution (V ω) M (hVb ω)
    rw [hVM_eq, hEV, ← integral_sub hG1 hQ1]
  -- Stage 12: per-ω product as a double integral over Icc×Icc.
  -- A(ω) = ∫ a, B(ω) = ∫ b imply A(ω)B(ω) = ∫∫ a·b.
  have hAB_int : ∀ ω : Ω,
      ((U ω + M) - (∫ ω', (U ω' + M) ∂P)) * ((V ω + M) - (∫ ω', (V ω' + M) ∂P))
      = ∫ t in Set.Icc (-M) M, ∫ s in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
    intro ω
    rw [hcenterU ω, hcenterV ω]
    have ha_meas : Measurable (fun t =>
        Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal) :=
      (Measurable.indicator measurable_const measurableSet_Iio).sub hPtail_meas
    have hb_meas : Measurable (fun s =>
        Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) :=
      (Measurable.indicator measurable_const measurableSet_Iio).sub hQtail_meas
    have hab_bdd : ∀ t : ℝ,
        ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t
          - (P {ω | U ω > t}).toReal‖ ≤ 2 := by
      intro t
      by_cases h : t ∈ Set.Iio (U ω)
      · rw [Set.indicator_of_mem h]
        calc ‖(1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal‖
            ≤ ‖(1 : ℝ → ℝ) t‖ + ‖(P {ω | U ω > t}).toReal‖ := norm_sub_le _ _
          _ ≤ 2 := by
            have e1 : ‖(1 : ℝ → ℝ) t‖ = 1 := by simp
            have e2 : ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
              rw [Real.norm_eq_abs]
              have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
                have hle' : P {ω | U ω > t} ≤ 1 := by
                  calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                    _ = 1 := measure_univ
                exact ENNReal.toReal_mono (by simp) hle'
              have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
              rw [abs_of_nonneg nn]
              exact hle
            rw [e1]
            linarith
      · rw [Set.indicator_of_notMem h]
        have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
          have hle' : P {ω | U ω > t} ≤ 1 := by
            calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          exact ENNReal.toReal_mono (by simp) hle'
        simp only [zero_sub]
        calc ‖-(P {ω | U ω > t}).toReal‖ = |(P {ω | U ω > t}).toReal| := by
              rw [Real.norm_eq_abs, abs_neg]
          _ ≤ 2 := by
            have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            linarith
    -- a(t), b(s) integrable on Icc (bounded + measurable); product = double integral.
    have ha_int : Integrable (fun t =>
        Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound ha_meas.aestronglyMeasurable 2
        (by filter_upwards with t using hab_bdd t)
    have hb_bdd : ∀ s : ℝ,
        ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s
          - (P {ω | V ω > s}).toReal‖ ≤ 2 := by
      intro s
      by_cases h : s ∈ Set.Iio (V ω)
      · rw [Set.indicator_of_mem h]
        calc ‖(1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal‖
            ≤ ‖(1 : ℝ → ℝ) s‖ + ‖(P {ω | V ω > s}).toReal‖ := norm_sub_le _ _
          _ ≤ 2 := by
            have e1 : ‖(1 : ℝ → ℝ) s‖ = 1 := by simp
            have e2 : ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
              rw [Real.norm_eq_abs]
              have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
                have hle' : P {ω | V ω > s} ≤ 1 := by
                  calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                    _ = 1 := measure_univ
                exact ENNReal.toReal_mono (by simp) hle'
              have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
              rw [abs_of_nonneg nn]
              exact hle
            rw [e1]
            linarith
      · rw [Set.indicator_of_notMem h]
        have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
          have hle' : P {ω | V ω > s} ≤ 1 := by
            calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          exact ENNReal.toReal_mono (by simp) hle'
        simp only [zero_sub]
        calc ‖-(P {ω | V ω > s}).toReal‖ = |(P {ω | V ω > s}).toReal| := by
              rw [Real.norm_eq_abs, abs_neg]
          _ ≤ 2 := by
            have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            linarith
    have hb_int : Integrable (fun s =>
        Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hb_meas.aestronglyMeasurable 2
        (by filter_upwards with s using hb_bdd s)
    -- (∫ a)(∫ b) = ∫∫ a·b by linearity in each variable (unconditional).
    have hprod : (∫ t in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal))
        * (∫ s in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal))
        = ∫ t in Set.Icc (-M) M, ∫ s in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
      rw [← integral_mul_const _ _]
      apply integral_congr_ae
      filter_upwards with t
      rw [← integral_const_mul _ _]
    exact hprod
  -- Stage 14: triple integrand H(ω,t,s) = a(ω,t)·b(ω,s); meas + bound + int.
  have ha_bd2 : ∀ (ω : Ω) (t : ℝ),
      ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t
        - (P {ω | U ω > t}).toReal‖ ≤ 2 := by
    intro ω t
    by_cases h : t ∈ Set.Iio (U ω)
    · rw [Set.indicator_of_mem h]
      calc ‖(1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal‖
          ≤ ‖(1 : ℝ → ℝ) t‖ + ‖(P {ω | U ω > t}).toReal‖ := norm_sub_le _ _
        _ ≤ 2 := by
          have e1 : ‖(1 : ℝ → ℝ) t‖ = 1 := by simp
          have e2 : ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
            rw [Real.norm_eq_abs]
            have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
              have hle' : P {ω | U ω > t} ≤ 1 := by
                calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                  _ = 1 := measure_univ
              exact ENNReal.toReal_mono (by simp) hle'
            have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            exact hle
          rw [e1]
          linarith
    · rw [Set.indicator_of_notMem h]
      have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
        have hle' : P {ω | U ω > t} ≤ 1 := by
          calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) hle'
      simp only [zero_sub]
      calc ‖-(P {ω | U ω > t}).toReal‖ = |(P {ω | U ω > t}).toReal| := by
            rw [Real.norm_eq_abs, abs_neg]
        _ ≤ 2 := by
          have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          linarith
  have hb_bd2 : ∀ (ω : Ω) (s : ℝ),
      ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s
        - (P {ω | V ω > s}).toReal‖ ≤ 2 := by
    intro ω s
    by_cases h : s ∈ Set.Iio (V ω)
    · rw [Set.indicator_of_mem h]
      calc ‖(1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal‖
          ≤ ‖(1 : ℝ → ℝ) s‖ + ‖(P {ω | V ω > s}).toReal‖ := norm_sub_le _ _
        _ ≤ 2 := by
          have e1 : ‖(1 : ℝ → ℝ) s‖ = 1 := by simp
          have e2 : ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
            rw [Real.norm_eq_abs]
            have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
              have hle' : P {ω | V ω > s} ≤ 1 := by
                calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                  _ = 1 := measure_univ
              exact ENNReal.toReal_mono (by simp) hle'
            have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            exact hle
          rw [e1]
          linarith
    · rw [Set.indicator_of_notMem h]
      have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
        have hle' : P {ω | V ω > s} ≤ 1 := by
          calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) hle'
      simp only [zero_sub]
      calc ‖-(P {ω | V ω > s}).toReal‖ = |(P {ω | V ω > s}).toReal| := by
            rw [Real.norm_eq_abs, abs_neg]
        _ ≤ 2 := by
          have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          linarith
  have ha_joint : Measurable (fun q : Ω × ℝ =>
      Set.indicator (Set.Iio (U q.1)) (1 : ℝ → ℝ) q.2 - (P {ω | U ω > q.2}).toReal) :=
    hF_meas.sub (hPtail_meas.comp measurable_snd)
  have hb_joint : Measurable (fun q : Ω × ℝ =>
      Set.indicator (Set.Iio (V q.1)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) :=
    hG_meas.sub (hQtail_meas.comp measurable_snd)
  -- Stage 15: H(ω,t,s) on Ω×(ℝ×ℝ); joint measurability + bound + integrability.
  -- Q2 is the square (vol|_Icc) × (vol|_Icc).
  have hH_meas : Measurable (fun p : Ω × (ℝ × ℝ) =>
      (Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
      * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal)) := by
    apply Measurable.mul
    · exact ha_joint.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact hb_joint.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hH_bdd : ∀ p : Ω × (ℝ × ℝ),
      ‖(Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
        * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal)‖ ≤ 4 := by
    intro p
    simp only [Pi.mul_apply, norm_mul]
    calc ‖Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1
          - (P {ω | U ω > p.2.1}).toReal‖
          * ‖Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2
          - (P {ω | V ω > p.2.2}).toReal‖
        ≤ 2 * 2 := mul_le_mul (ha_bd2 p.1 p.2.1) (hb_bd2 p.1 p.2.2)
          (by positivity) (by linarith)
      _ = 4 := by norm_num
  have hH_int : Integrable (fun p : Ω × (ℝ × ℝ) =>
      (Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
      * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal))
      (P.prod ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) :=
    Integrable.of_bound hH_meas.aestronglyMeasurable 4
      (by filter_upwards with p using hH_bdd p)
  -- Stage 16: swap; per-ω Q2 integral = A·B; inner = indicator cov.
  have hH_unc : Integrable
      (Function.uncurry fun ω (q : ℝ × ℝ) =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal))
      (P.prod ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) :=
    hH_int
  have hswap2 := integral_integral_swap hH_unc
  -- Stage 17: per-ω Q2 integral = A(ω)·B(ω) via integral_prod + hAB_int.
  have hperω : ∀ ω : Ω,
      (∫ q : ℝ × ℝ,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))))
      = ((U ω + M) - (∫ ω', (U ω' + M) ∂P)) * ((V ω + M) - (∫ ω', (V ω' + M) ∂P)) := by
    intro ω
    have hmq : Measurable (fun q : ℝ × ℝ =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)) := by
      apply Measurable.mul
      · exact ((Measurable.indicator measurable_const measurableSet_Iio).sub hPtail_meas).comp
          measurable_fst
      · exact ((Measurable.indicator measurable_const measurableSet_Iio).sub hQtail_meas).comp
          measurable_snd
    have hbq : ∀ q : ℝ × ℝ,
        ‖(Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)‖ ≤ 4 := by
      intro q
      simp only [Pi.mul_apply, norm_mul]
      calc ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal‖
            * ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal‖
          ≤ 2 * 2 := mul_le_mul (ha_bd2 ω q.1) (hb_bd2 ω q.2)
            (by positivity) (by linarith)
        _ = 4 := by norm_num
    have hint_q : Integrable (fun q : ℝ × ℝ =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal))
        ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) :=
      Integrable.of_bound hmq.aestronglyMeasurable 4
        (by filter_upwards with q using hbq q)
    rw [integral_prod _ hint_q]
    exact (hAB_int ω).symm
  -- Stage 18: LHS of swap = cov(U+M,V+M); inner identification + bound.
  have hLHS2 : (∫ ω, ∫ q : ℝ × ℝ,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) ∂P)
      = cov[fun ω => U ω + M, fun ω => V ω + M; P] := by
    apply integral_congr_ae
    filter_upwards with ω
    exact hperω ω
  have hinner_eq : ∀ q : ℝ × ℝ,
      (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
      = (P ({ω | U ω > q.1} ∩ {ω | V ω > q.2})).toReal
        - (P {ω | U ω > q.1}).toReal * (P {ω | V ω > q.2}).toReal := by
    intro q
    have e1 : ∀ ω, Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1
        = Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : U ω > q.1
      · have hm : q.1 ∈ Set.Iio (U ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | U ω > q.1} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : q.1 ∉ Set.Iio (U ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | U ω > q.1} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    have e2 : ∀ ω, Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2
        = Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : V ω > q.2
      · have hm : q.2 ∈ Set.Iio (V ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | V ω > q.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : q.2 ∉ Set.Iio (V ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | V ω > q.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    have eU : P[Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ))]
        = (P {ω | U ω > q.1}).toReal := by
      rw [integral_indicator_const _ (hAt_amb q.1)]
      simp [Measure.real_def]
    have eV : P[Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ))]
        = (P {ω | V ω > q.2}).toReal := by
      rw [integral_indicator_const _ (hBs_amb q.2)]
      simp [Measure.real_def]
    have hcov : cov[Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ)),
        Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ)); P]
        = (P ({ω | U ω > q.1} ∩ {ω | V ω > q.2})).toReal
          - (P {ω | U ω > q.1}).toReal * (P {ω | V ω > q.2}).toReal :=
      _root_.NumberBoundedAlphaPort_ProbabilityTheory_cov_indicator_eq.solution P _ _ (hAt_amb q.1) (hBs_amb q.2)
    simp only [e1, e2]
    unfold ProbabilityTheory.covariance at hcov
    conv_lhs => rw [← eU, ← eV]
    exact hcov
  -- Stage 19: pointwise bound + area + constants-vanish + conclusion.
  have hinner_bd : ∀ q : ℝ × ℝ,
      ‖(∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)‖
        ≤ alphaMixingCoef P Y n := by
    intro q
    rw [Real.norm_eq_abs, hinner_eq q]
    exact hα_ts q.1 q.2
  -- cov(U+M,V+M) = ∫_Q2 inner by (hLHS2 via hperω) + swap.
  have hcovQ : cov[fun ω => U ω + M, fun ω => V ω + M; P]
      = ∫ q : ℝ × ℝ,
        (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) := by
    have e1 : cov[fun ω => U ω + M, fun ω => V ω + M; P]
        = ∫ ω, (∫ q : ℝ × ℝ,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
          ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hperω ω).symm
    rw [e1]
    exact hswap2
  -- Stage 20: area bound + constants-vanish + conclusion.
  have hUint : Integrable U P := hU2.integrable (by norm_num)
  have hVint : Integrable V P := hV2.integrable (by norm_num)
  have hUV : cov[fun ω => U ω + M, fun ω => V ω + M; P] = cov[U, V; P] := by
    rw [covariance_add_const_left hUint M, covariance_add_const_right hVint M]
  have hvolQ2 : (((volume.restrict (Set.Icc (-M) M)).prod
      (volume.restrict (Set.Icc (-M) M))) Set.univ).toReal = 4 * M ^ 2 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ,
      Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ M - -M),
      ENNReal.toReal_ofReal (mul_nonneg (by linarith : (0:ℝ) ≤ M - -M) (by linarith : (0:ℝ) ≤ M - -M))]
    ring
  have hfinal : ‖cov[fun ω => U ω + M, fun ω => V ω + M; P]‖ ≤ 4 * M ^ 2 * alphaMixingCoef P Y n := by
    have hle : ∀ᵐ q : ℝ × ℝ
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))),
        ‖(∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)‖
          ≤ alphaMixingCoef P Y n := by
      filter_upwards with q
      exact hinner_bd q
    calc ‖cov[fun ω => U ω + M, fun ω => V ω + M; P]‖
        = ‖∫ q : ℝ × ℝ,
          (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
            * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
          ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))‖ := by
          rw [hcovQ]
      _ ≤ alphaMixingCoef P Y n
          * (((volume.restrict (Set.Icc (-M) M)).prod
            (volume.restrict (Set.Icc (-M) M))).real Set.univ) :=
        norm_integral_le_of_norm_le_const hle
      _ = 4 * M ^ 2 * alphaMixingCoef P Y n := by
        rw [Measure.real_def, hvolQ2]
        ring
  rw [Real.norm_eq_abs] at hfinal
  rw [← hUV]
  exact hfinal


end NumberBoundedAlphaPort_MarkovChainCLT_alpha_cov_bounded


namespace NumberBoundedAlphaPort_MarkovChainCLT_stationary_mean_transfer

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) :
    ∀ k : ℕ, ∫ ω, Y k ω ∂P = 0 := by
  intro k
  have hmap : P.map (Y k) = P.map (Y 0) := by
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have h1 : ∫ x, x ∂(P.map (Y k)) = ∫ ω, Y k ω ∂P :=
    integral_map (hY k).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  have h2 : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
    integral_map (hY 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  rw [← h1, hmap, h2, hcent]

end NumberBoundedAlphaPort_MarkovChainCLT_stationary_mean_transfer


namespace NumberBoundedAlphaPort_MarkovChainCLT_stationary_memLp_transfer

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) :
    ∀ k : ℕ, MemLp (Y k) 2 P := by
  intro k
  have hmap : P.map (Y k) = P.map (Y 0) := by
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff (measurable_id.aestronglyMeasurable)
      (hY 0).aemeasurable).2 hL2
  have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by
    rw [hmap]
    exact h0
  exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable)
    (hY k).aemeasurable).1 hk

end NumberBoundedAlphaPort_MarkovChainCLT_stationary_memLp_transfer


namespace NumberBoundedAlphaPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

-- Scratch: direct proof of `_root_.NumberBoundedAlphaPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov.solution`.
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)) :
    Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)) := by
  have hmap : ∀ k, P.map (Y k) = P.map (Y 0) := by
    intro k
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have hmemLp : ∀ k, MemLp (Y k) 2 P := by
    intro k
    have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
      (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY 0).aemeasurable).2 hL2
    have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by rw [hmap k]; exact h0
    exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY k).aemeasurable).1 hk
  have hmean : ∀ k, ∫ ω, Y k ω ∂P = 0 := by
    intro k
    have h1 : ∫ x, x ∂(P.map (Y k)) = ∫ ω, Y k ω ∂P :=
      integral_map (hY k).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    have h2 : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
      integral_map (hY 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    rw [← h1, hmap k, h2, hcent]
  set c : ℕ → ℝ := fun k => ∫ ω, Y 0 ω * Y k ω ∂P with hc
  have hc_def : ∀ k, c k = ∫ ω, Y 0 ω * Y k ω ∂P := fun k => rfl
  have hpair : ∀ i d : ℕ, ∫ ω, Y i ω * Y (i + d) ω ∂P = c d := by
    intro i d
    have hgm : Measurable (fun f : ℕ → ℝ => f 0 * f d) :=
      (measurable_pi_apply 0).mul (measurable_pi_apply d)
    have hmeasi : Measurable (fun ω n => Y (n + i) ω) :=
      measurable_pi_lambda _ fun n => hY (n + i)
    have hmeas0 : Measurable (fun ω n => Y n ω) :=
      measurable_pi_lambda _ fun n => hY n
    have e1 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y (n + i) ω) P)
        = ∫ ω, Y i ω * Y (i + d) ω ∂P := by
      rw [integral_map hmeasi.aemeasurable hgm.aestronglyMeasurable]
      apply integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show Y (0 + i) ω * Y (d + i) ω = Y i ω * Y (i + d) ω
      rw [Nat.zero_add, Nat.add_comm d i]
    have e2 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y n ω) P)
        = ∫ ω, Y 0 ω * Y d ω ∂P := by
      rw [integral_map hmeas0.aemeasurable hgm.aestronglyMeasurable]
    rw [hc_def d]
    rw [hstat i] at e1
    rw [e2] at e1
    exact e1.symm
  have hcov : ∀ i j : ℕ, i ≤ j → cov[Y i, Y j; P] = c (j - i) := by
    intro i j hij
    have hji : j = i + (j - i) := (Nat.add_sub_cancel' hij).symm
    rw [covariance]
    simp only [hmean i, hmean j, sub_zero]
    conv_lhs => rw [hji]
    exact hpair i (j - i)
  have hF : ∀ n : ℕ, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P])
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcol : ∑ i ∈ Finset.range n, cov[Y i, Y n; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e1 : ∀ i ∈ Finset.range n, cov[Y i, Y n; P] = c ((n - 1 - i) + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hiN : i ≤ n := Nat.le_of_lt hi
          have h := hcov i n hiN
          have hni : n - i = (n - 1 - i) + 1 := by omega
          rw [hni] at h
          exact h
        rw [Finset.sum_congr rfl e1]
        exact Finset.sum_range_reflect (fun j => c (j + 1)) n
      have hrow : ∑ j ∈ Finset.range n, cov[Y n, Y j; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e : ∀ j ∈ Finset.range n, cov[Y n, Y j; P] = cov[Y j, Y n; P] :=
          fun j _ => covariance_comm (Y n) (Y j)
        rw [Finset.sum_congr rfl e]
        exact hcol
      have hdiag : cov[Y n, Y n; P] = c 0 := by
        have h := hcov n n le_rfl
        simpa using h
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih, hcol, hrow, hdiag]
      push_cast
      ring
  have hV : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P] :=
    fun n => variance_sum' (fun i _ => hmemLp i)
  have hVD : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) :=
    fun n => (hV n).trans (hF n)
  have hsig : seqAsymptoticVariance P Y = c 0 + 2 * ∑' k, c (k + 1) := by
    have hc0 : c 0 = ∫ ω, Y 0 ω * Y 0 ω ∂P := rfl
    have hsq : (∫ ω, (Y 0 ω) ^ 2 ∂P) = ∫ ω, Y 0 ω * Y 0 ω ∂P := by
      congr 1; ext ω; rw [pow_two]
    show (∫ ω, (Y 0 ω) ^ 2 ∂P) + 2 * ∑' k : ℕ, ∫ ω, Y 0 ω * Y (k + 1) ω ∂P = _
    rw [hsq, hc0]
  rw [hsig]
  have hD : Tendsto (fun m => ∑ k ∈ Finset.range m, c (k + 1)) atTop
      (𝓝 (∑' k, c (k + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hces := hD.cesaro
  have hadd : Tendsto
      (fun n : ℕ => c 0 + 2 * ((n⁻¹ : ℝ) * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1)))
      atTop (𝓝 (c 0 + 2 * ∑' k, c (k + 1))) :=
    tendsto_const_nhds.add (hces.const_mul 2)
  refine Filter.Tendsto.congr' ?h hadd
  filter_upwards [eventually_ge_atTop 1] with n hn
  show c 0 + 2 * ((n⁻¹ : ℝ) * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1))
    = Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ)
  rw [hVD n]
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end NumberBoundedAlphaPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov


namespace NumberBoundedAlphaPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  -- Work at level M := |B|; truncations agree a.e. and inherit zero means.
  have hM0 : (0:ℝ) ≤ |B| := abs_nonneg _
  -- Per-k bound: |∫Y0Y_{k+1}| ≤ 4|B|²·α(k+1).
  have hkey : ∀ k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|
      ≤ 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1) := by
    intro k
    set T : ℝ → ℝ := fun y => max (-|B|) (min y |B|) with hTdef
    have hTm : Measurable T :=
      (Continuous.max continuous_const
        (continuous_id.min continuous_const)).measurable
    have hTb : ∀ y : ℝ, |T y| ≤ |B| := by
      intro y
      have h1 : -|B| ≤ T y := le_max_left _ _
      have h2 : T y ≤ |B| := by
        apply max_le _ _
        · linarith [abs_nonneg B]
        · exact min_le_right _ _
      exact abs_le.mpr ⟨h1, h2⟩
    set U' : Ω → ℝ := fun ω => T (Y 0 ω) with hU'def
    set V' : Ω → ℝ := fun ω => T (Y (k + 1) ω) with hV'def
    -- Truncations agree a.e. (|Y| < B ≤ |B| a.e. ⇒ trunc = id there).
    have hae0 : U' =ᵐ[P] Y 0 := by
      filter_upwards [hB 0] with ω hω
      show T (Y 0 ω) = Y 0 ω
      have hle : |Y 0 ω| ≤ |B| := le_trans hω.le (le_abs_self B)
      have h1 : min (Y 0 ω) |B| = Y 0 ω := min_eq_left (abs_le.mp hle).2
      have h2 : max (-|B|) (Y 0 ω) = Y 0 ω :=
        max_eq_right (by linarith [(abs_le.mp hle).1])
      show max (-|B|) (min (Y 0 ω) |B|) = Y 0 ω
      rw [h1]
      exact h2
    have hae1 : V' =ᵐ[P] Y (k + 1) := by
      filter_upwards [hB (k + 1)] with ω hω
      show T (Y (k + 1) ω) = Y (k + 1) ω
      have hle : |Y (k + 1) ω| ≤ |B| := le_trans hω.le (le_abs_self B)
      have h1 : min (Y (k + 1) ω) |B| = Y (k + 1) ω :=
        min_eq_left (abs_le.mp hle).2
      have h2 : max (-|B|) (Y (k + 1) ω) = Y (k + 1) ω :=
        max_eq_right (by linarith [(abs_le.mp hle).1])
      show max (-|B|) (min (Y (k + 1) ω) |B|) = Y (k + 1) ω
      rw [h1]
      exact h2
    -- Truncations inherit zero means via a.e. equality.
    have hEU' : ∫ ω, U' ω ∂P = 0 := by
      have e : (∫ ω, U' ω ∂P) = ∫ ω, Y 0 ω ∂P :=
        integral_congr_ae hae0
      rw [e]
      exact hcent
    have hEV' : ∫ ω, V' ω ∂P = 0 := by
      have e : (∫ ω, V' ω ∂P) = ∫ ω, Y (k + 1) ω ∂P :=
        integral_congr_ae hae1
      rw [e]
      exact _root_.NumberBoundedAlphaPort_MarkovChainCLT_stationary_mean_transfer.solution P Y hY hstat hcent (k + 1)
    -- L² via everywhere-boundedness on a probability space.
    have hTm : Measurable T :=
      (Continuous.max continuous_const
        (continuous_id.min continuous_const)).measurable
    have hU'm : Measurable U' := hTm.comp (hY 0)
    have hV'm : Measurable V' := hTm.comp (hY (k + 1))
    have hU'L2 : MemLp U' 2 P :=
      MemLp.of_bound hU'm.aestronglyMeasurable _ (by
        filter_upwards with ω
        calc ‖U' ω‖ = |U' ω| := Real.norm_eq_abs _
          _ ≤ |B| := hTb _)
    have hV'L2 : MemLp V' 2 P :=
      MemLp.of_bound hV'm.aestronglyMeasurable _ (by
        filter_upwards with ω
        calc ‖V' ω‖ = |V' ω| := Real.norm_eq_abs _
          _ ≤ |B| := hTb _)
    -- Past/future exact measurability for the bounded lemma (lag k+1 at j=0).
    -- (Lattice facts inlined: the platform copies live in the wrong env.)
    have hcoord_past : Measurable[processSigma Y (Set.Iic 0)] (Y 0) := by
      refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic 0) =>
        MeasurableSpace.comap (Y i) inferInstance) 0 (Set.mem_Iic.2 le_rfl)
    have hcoord_fut : Measurable[processSigma Y (Set.Ici (k + 1))] (Y (k + 1)) := by
      refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
      refine le_iSup₂ (f := fun i (_ : i ∈ Set.Ici (k + 1)) =>
        MeasurableSpace.comap (Y i) inferInstance) (k + 1) ?_
      simp
    have hU'past : Measurable[processSigma Y (Set.Iic 0)] U' :=
      hTm.comp hcoord_past
    have hV'fut : Measurable[processSigma Y (Set.Ici (0 + (k + 1)))] V' := by
      have h : Measurable[processSigma Y (Set.Ici (k + 1))] V' :=
        hTm.comp hcoord_fut
      have e : (0 : ℕ) + (k + 1) = k + 1 := Nat.zero_add _
      rw [e]
      exact h
    -- Chain: plain = trunc integral = cov = bounded.
    have hInt : (∫ ω, Y 0 ω * Y (k + 1) ω ∂P)
        = ∫ ω, U' ω * V' ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hae0, hae1] with ω h0 h1
      rw [h0, h1]
    have hCov : (∫ ω, U' ω * V' ω ∂P) = cov[U', V'; P] := by
      have h := covariance_eq_sub hU'L2 hV'L2
      rw [hEU', hEV', mul_zero, sub_zero] at h
      exact h.symm
    calc |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| = |cov[U', V'; P]| := by
          rw [hInt, hCov]
      _ ≤ 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1) := by
          have hU'b : ∀ ω, |U' ω| ≤ |B| := fun ω => hTb (Y 0 ω)
          have hV'b : ∀ ω, |V' ω| ≤ |B| := fun ω => hTb (Y (k + 1) ω)
          exact _root_.NumberBoundedAlphaPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0 U' V'
            hU'past hV'fut _ (abs_nonneg _) hU'b hV'b
  -- Comparison with the summable α series.
  have hsum : Summable (fun k : ℕ => 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1)) :=
    ((summable_nat_add_iff 1).2 hα).mul_left _
  exact Summable.of_norm_bounded hsum fun k => by simpa using hkey k

end NumberBoundedAlphaPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha


namespace NumberBoundedAlphaPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  have hL2 : MemLp (Y 0) 2 P := by
    have hsq_meas : Measurable (fun ω => (Y 0 ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using (hY 0).mul (hY 0)
    have hInt : Integrable (fun ω => (Y 0 ω) ^ 2) P := by
      refine Integrable.mono' (g := fun _ => B ^ 2) (integrable_const _)
        hsq_meas.aestronglyMeasurable ?_
      filter_upwards [hB 0] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hB0 : 0 ≤ B
      · exact le_of_lt (sq_lt_sq' (abs_lt.mp hω).1 (abs_lt.mp hω).2)
      · have hBneg : B < 0 := lt_of_not_ge hB0
        have hcon : (0 : ℝ) ≤ |Y 0 ω| := abs_nonneg _
        linarith
    exact (memLp_two_iff_integrable_sq (hY 0).aestronglyMeasurable).mpr hInt
  have hlim :=
    _root_.NumberBoundedAlphaPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov.solution P Y hY hstat hcent hL2 hsum
  exact clt_of_var_limit_of_bounded P Y hY hstat hcent B hB hα hlim hvar

end NumberBoundedAlphaPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha

section OwnCandidate

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 5, condition 1 (Ibragimov–Linnik bounded case), reduced to the
covariance-summability and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := _root_.NumberBoundedAlphaPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha.solution
    P Y hY hstat hcent B hB hα
  refine ⟨hsum, fun hvar => ?_⟩
  exact _root_.NumberBoundedAlphaPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha.solution
    P Y hY hstat hcent B hB hα hsum hvar

end OwnCandidate
#print axioms solution