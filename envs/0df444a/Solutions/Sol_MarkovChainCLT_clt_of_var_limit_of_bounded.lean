-- Prove2me | solution 1 for MarkovChainCLT.clt_of_var_limit_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:11:56.483109+00:00
-- url     : https://prove2.me/submissions/d017e0d8-c04c-4e16-92da-44b53d2b7391

import Definitions.Def_MixingCoefficients
import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_nonneg
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NumberBoundedPort_LayerCake_bounded_layercake_identity

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

end NumberBoundedPort_LayerCake_bounded_layercake_identity


namespace NumberBoundedPort_LayerCake_expectation_add_const

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
    fun ω => _root_.NumberBoundedPort_LayerCake_bounded_layercake_identity.solution (W ω) M (hWb ω)
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

end NumberBoundedPort_LayerCake_expectation_add_const


namespace NumberBoundedPort_ProbabilityTheory_cov_indicator_eq

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

end NumberBoundedPort_ProbabilityTheory_cov_indicator_eq


namespace NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable

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

end NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable


namespace NumberBoundedPort_MarkovChainCLT_alpha_indicator_cov_le

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

end NumberBoundedPort_MarkovChainCLT_alpha_indicator_cov_le


namespace NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded

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
    _root_.NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
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
    fun t s => _root_.NumberBoundedPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y n k _ _ (hAt t) (hBs s)
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
    fun ω => _root_.NumberBoundedPort_LayerCake_bounded_layercake_identity.solution (U ω) M (hUb ω)
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
    _root_.NumberBoundedPort_LayerCake_expectation_add_const.solution P V hVm M (fun ω => hVb ω)
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
      _root_.NumberBoundedPort_LayerCake_bounded_layercake_identity.solution (V ω) M (hVb ω)
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
      _root_.NumberBoundedPort_ProbabilityTheory_cov_indicator_eq.solution P _ _ (hAt_amb q.1) (hBs_amb q.2)
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


end NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded


namespace NumberBoundedPort_MarkovChainCLT_alphaMixingCoef_antitone

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Enlarging the index set enlarges the σ-algebra generated by the corresponding
coordinates. -/
private theorem processSigma_mono' {Ω E : Type*} [MeasurableSpace E] (Y : ℕ → Ω → E)
    {s t : Set ℕ} (hst : s ⊆ t) : processSigma Y s ≤ processSigma Y t :=
  iSup₂_le fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ t) => MeasurableSpace.comap (Y i) inferInstance) i (hst hi)

theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) :
    Antitone (fun n => alphaMixingCoef P Y n) := by
  intro m n hmn
  refine csSup_le_csSup ?_ ?_ ?_
  · -- the family defining `α(m)` is bounded above by `1`
    refine ⟨1, ?_⟩
    rintro r ⟨k, A, B, -, -, rfl⟩
    have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ (A ∩ B)))
    have hA1 : (P A).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ A))
    have hB1 : (P B).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ B))
    have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
    have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
    have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> nlinarith
  · -- the family defining `α(n)` is nonempty
    exact ⟨0, 0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
      @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
  · -- every pair admissible at lag `n` is admissible at lag `m ≤ n`
    rintro r ⟨k, A, B, hA, hB, rfl⟩
    exact ⟨k, A, B, hA, processSigma_mono' Y (Set.Ici_subset_Ici.2 (by omega)) _ hB, rfl⟩

end NumberBoundedPort_MarkovChainCLT_alphaMixingCoef_antitone


namespace NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded_complex

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Rescaled form of the bounded covariance inequality: separate bounds for the two
variables. -/
private theorem alpha_cov_bounded_aux (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUb : ∀ ω, |U ω| ≤ A) (hVb : ∀ ω, |V ω| ≤ B) :
    |cov[U, V; P]| ≤ 4 * A * B * alphaMixingCoef P Y n := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hU0 : U = fun _ => (0 : ℝ) := by
      funext ω
      have := hUb ω
      rw [← hA0] at this
      exact abs_nonpos_iff.mp this
    rw [hU0]
    have : cov[fun _ => (0 : ℝ), V; P] = 0 := covariance_const_left 0
    rw [this, ← hA0]
    simp
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have hV0 : V = fun _ => (0 : ℝ) := by
      funext ω
      have := hVb ω
      rw [← hB0] at this
      exact abs_nonpos_iff.mp this
    rw [hV0]
    have : cov[U, fun _ => (0 : ℝ); P] = 0 := covariance_const_right 0
    rw [this, ← hB0]
    simp
  · set U' : Ω → ℝ := fun ω => A⁻¹ * U ω with hU'
    set V' : Ω → ℝ := fun ω => B⁻¹ * V ω with hV'
    have hU'meas : Measurable[processSigma Y (Set.Iic k)] U' := by
      exact (measurable_const.mul hU : Measurable[processSigma Y (Set.Iic k)] _)
    have hV'meas : Measurable[processSigma Y (Set.Ici (k + n))] V' := by
      exact (measurable_const.mul hV : Measurable[processSigma Y (Set.Ici (k + n))] _)
    have hU'b : ∀ ω, |U' ω| ≤ 1 := by
      intro ω
      rw [hU', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A⁻¹)]
      rw [inv_mul_le_iff₀ hApos]
      simpa using hUb ω
    have hV'b : ∀ ω, |V' ω| ≤ 1 := by
      intro ω
      rw [hV', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ B⁻¹)]
      rw [inv_mul_le_iff₀ hBpos]
      simpa using hVb ω
    have hmain := _root_.NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY n k U' V' hU'meas hV'meas 1
      zero_le_one hU'b hV'b
    have hcov : cov[U', V'; P] = A⁻¹ * B⁻¹ * cov[U, V; P] := by
      rw [hU', hV', covariance_const_mul_left, covariance_const_mul_right, ← mul_assoc]
    rw [hcov] at hmain
    have habs : |A⁻¹ * B⁻¹ * cov[U, V; P]| = A⁻¹ * B⁻¹ * |cov[U, V; P]| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A⁻¹),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ B⁻¹)]
    rw [habs] at hmain
    have hstep : A * B * (A⁻¹ * B⁻¹ * |cov[U, V; P]|)
        ≤ A * B * (4 * 1 ^ 2 * alphaMixingCoef P Y n) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    calc |cov[U, V; P]| = A * B * (A⁻¹ * B⁻¹ * |cov[U, V; P]|) := by
          field_simp
      _ ≤ A * B * (4 * 1 ^ 2 * alphaMixingCoef P Y n) := hstep
      _ = 4 * A * B * alphaMixingCoef P Y n := by ring


/-- Complex-valued form of the bounded covariance inequality under strong mixing. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℂ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUb : ∀ ω, ‖U ω‖ ≤ A) (hVb : ∀ ω, ‖V ω‖ ≤ B) :
    ‖(∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)‖
      ≤ 16 * A * B * alphaMixingCoef P Y n := by
  classical
  set u1 : Ω → ℝ := fun ω => (U ω).re with hu1def
  set u2 : Ω → ℝ := fun ω => (U ω).im with hu2def
  set v1 : Ω → ℝ := fun ω => (V ω).re with hv1def
  set v2 : Ω → ℝ := fun ω => (V ω).im with hv2def
  have hu1 : Measurable[processSigma Y (Set.Iic k)] u1 := Complex.measurable_re.comp hU
  have hu2 : Measurable[processSigma Y (Set.Iic k)] u2 := Complex.measurable_im.comp hU
  have hv1 : Measurable[processSigma Y (Set.Ici (k + n))] v1 := Complex.measurable_re.comp hV
  have hv2 : Measurable[processSigma Y (Set.Ici (k + n))] v2 := Complex.measurable_im.comp hV
  have hUm : Measurable U := hU.mono (_root_.NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  have hVm : Measurable V := hV.mono (_root_.NumberBoundedPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  have hu1m : Measurable u1 := Complex.measurable_re.comp hUm
  have hu2m : Measurable u2 := Complex.measurable_im.comp hUm
  have hv1m : Measurable v1 := Complex.measurable_re.comp hVm
  have hv2m : Measurable v2 := Complex.measurable_im.comp hVm
  have hu1b : ∀ ω, |u1 ω| ≤ A := fun ω => (Complex.abs_re_le_norm _).trans (hUb ω)
  have hu2b : ∀ ω, |u2 ω| ≤ A := fun ω => (Complex.abs_im_le_norm _).trans (hUb ω)
  have hv1b : ∀ ω, |v1 ω| ≤ B := fun ω => (Complex.abs_re_le_norm _).trans (hVb ω)
  have hv2b : ∀ ω, |v2 ω| ≤ B := fun ω => (Complex.abs_im_le_norm _).trans (hVb ω)
  -- the four covariance bounds
  have hcov11 := alpha_cov_bounded_aux P Y hY n k u1 v1 hu1 hv1 A B hA hB hu1b hv1b
  have hcov22 := alpha_cov_bounded_aux P Y hY n k u2 v2 hu2 hv2 A B hA hB hu2b hv2b
  have hcov12 := alpha_cov_bounded_aux P Y hY n k u1 v2 hu1 hv2 A B hA hB hu1b hv2b
  have hcov21 := alpha_cov_bounded_aux P Y hY n k u2 v1 hu2 hv1 A B hA hB hu2b hv1b
  -- integrability
  have hUint : Integrable U P :=
    (MemLp.of_bound (p := 1) hUm.aestronglyMeasurable A (Filter.Eventually.of_forall hUb)).integrable
      le_rfl
  have hVint : Integrable V P :=
    (MemLp.of_bound (p := 1) hVm.aestronglyMeasurable B (Filter.Eventually.of_forall hVb)).integrable
      le_rfl
  have hUVint : Integrable (fun ω => U ω * V ω) P := by
    refine (MemLp.of_bound (p := 1) (hUm.mul hVm).aestronglyMeasurable (A * B)
      (Filter.Eventually.of_forall fun ω => ?_)).integrable le_rfl
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hUb ω) (hVb ω) (norm_nonneg _) hA
  have hmemLp : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → MemLp f 2 P := by
    intro f C hf hfb
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => hfb ω)
  have hu1L : MemLp u1 2 P := hmemLp u1 A hu1m hu1b
  have hu2L : MemLp u2 2 P := hmemLp u2 A hu2m hu2b
  have hv1L : MemLp v1 2 P := hmemLp v1 B hv1m hv1b
  have hv2L : MemLp v2 2 P := hmemLp v2 B hv2m hv2b
  have hprod : ∀ (f g : Ω → ℝ) (C D : ℝ), Measurable f → Measurable g →
      (∀ ω, |f ω| ≤ C) → (∀ ω, |g ω| ≤ D) → Integrable (fun ω => f ω * g ω) P := by
    intro f g C D hf hg hfb hgb
    refine (MemLp.of_bound (p := 1) (hf.mul hg).aestronglyMeasurable (C * D)
      (Filter.Eventually.of_forall fun ω => ?_)).integrable le_rfl
    have h1 : |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
    have h2 : |f ω| * |g ω| ≤ C * D :=
      mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) ((abs_nonneg _).trans (hfb ω))
    simpa [Real.norm_eq_abs, h1] using h2
  have h11 : Integrable (fun ω => u1 ω * v1 ω) P := hprod u1 v1 A B hu1m hv1m hu1b hv1b
  have h22 : Integrable (fun ω => u2 ω * v2 ω) P := hprod u2 v2 A B hu2m hv2m hu2b hv2b
  have h12 : Integrable (fun ω => u1 ω * v2 ω) P := hprod u1 v2 A B hu1m hv2m hu1b hv2b
  have h21 : Integrable (fun ω => u2 ω * v1 ω) P := hprod u2 v1 A B hu2m hv1m hu2b hv1b
  -- real and imaginary parts of the integrals
  have hUVre : (∫ ω, U ω * V ω ∂P).re
      = (∫ ω, u1 ω * v1 ω ∂P) - (∫ ω, u2 ω * v2 ω ∂P) := by
    have h := Complex.reCLM.integral_comp_comm hUVint
    simp only [Complex.reCLM_apply] at h
    rw [← h]
    simp only [Complex.mul_re, hu1def, hu2def, hv1def, hv2def]
    exact integral_sub h11 h22
  have hUVim : (∫ ω, U ω * V ω ∂P).im
      = (∫ ω, u1 ω * v2 ω ∂P) + (∫ ω, u2 ω * v1 ω ∂P) := by
    have h := Complex.imCLM.integral_comp_comm hUVint
    simp only [Complex.imCLM_apply] at h
    rw [← h]
    simp only [Complex.mul_im, hu1def, hu2def, hv1def, hv2def]
    exact integral_add h12 h21
  have hUre : (∫ ω, U ω ∂P).re = ∫ ω, u1 ω ∂P := by
    have h := Complex.reCLM.integral_comp_comm hUint
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hUim : (∫ ω, U ω ∂P).im = ∫ ω, u2 ω ∂P := by
    have h := Complex.imCLM.integral_comp_comm hUint
    simp only [Complex.imCLM_apply] at h
    exact h.symm
  have hVre : (∫ ω, V ω ∂P).re = ∫ ω, v1 ω ∂P := by
    have h := Complex.reCLM.integral_comp_comm hVint
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hVim : (∫ ω, V ω ∂P).im = ∫ ω, v2 ω ∂P := by
    have h := Complex.imCLM.integral_comp_comm hVint
    simp only [Complex.imCLM_apply] at h
    exact h.symm
  -- the covariances as integral differences
  have hc11 : cov[u1, v1; P] = (∫ ω, u1 ω * v1 ω ∂P) - (∫ ω, u1 ω ∂P) * (∫ ω, v1 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu1L hv1L
  have hc22 : cov[u2, v2; P] = (∫ ω, u2 ω * v2 ω ∂P) - (∫ ω, u2 ω ∂P) * (∫ ω, v2 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu2L hv2L
  have hc12 : cov[u1, v2; P] = (∫ ω, u1 ω * v2 ω ∂P) - (∫ ω, u1 ω ∂P) * (∫ ω, v2 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu1L hv2L
  have hc21 : cov[u2, v1; P] = (∫ ω, u2 ω * v1 ω ∂P) - (∫ ω, u2 ω ∂P) * (∫ ω, v1 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu2L hv1L
  set D : ℂ := (∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) with hD
  have hDre : D.re = cov[u1, v1; P] - cov[u2, v2; P] := by
    rw [hD, Complex.sub_re, Complex.mul_re, hUVre, hUre, hUim, hVre, hVim, hc11, hc22]
    ring
  have hDim : D.im = cov[u1, v2; P] + cov[u2, v1; P] := by
    rw [hD, Complex.sub_im, Complex.mul_im, hUVim, hUre, hUim, hVre, hVim, hc12, hc21]
    ring
  have habs1 : |D.re| ≤ 4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n := by
    rw [hDre]
    calc |cov[u1, v1; P] - cov[u2, v2; P]| ≤ |cov[u1, v1; P]| + |cov[u2, v2; P]| :=
          abs_sub _ _
      _ ≤ _ := add_le_add hcov11 hcov22
  have habs2 : |D.im| ≤ 4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n := by
    rw [hDim]
    calc |cov[u1, v2; P] + cov[u2, v1; P]| ≤ |cov[u1, v2; P]| + |cov[u2, v1; P]| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add hcov12 hcov21
  calc ‖D‖ ≤ |D.re| + |D.im| := Complex.norm_le_abs_re_add_abs_im D
    _ ≤ (4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n)
        + (4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n) :=
      add_le_add habs1 habs2
    _ = 16 * A * B * alphaMixingCoef P Y n := by ring


end NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded_complex


namespace NumberBoundedPort_MarkovChainCLT_stationary_mean_transfer

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

end NumberBoundedPort_MarkovChainCLT_stationary_mean_transfer


namespace NumberBoundedPort_MarkovChainCLT_stationary_memLp_transfer

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

end NumberBoundedPort_MarkovChainCLT_stationary_memLp_transfer


namespace NumberBoundedPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

-- Finite-selection covariance bound for the small-block argument.
-- The stationarity transport follows the accepted Prove2Me proof of
-- MarkovChainCLT.var_partialSum_div_tendsto_of_summable_cov (submission
-- 22190ef3-0b53-4770-9441-4c54c00d05a1). The arbitrary-index row bound is proved below.
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|))
    (s : Finset ℕ) :
    Var[∑ i ∈ s, Y i; P] ≤ (s.card : ℝ) *
      ((∫ ω, (Y 0 ω) ^ 2 ∂P) +
        2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) := by
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
  classical
  let C : ℝ := ∑' k : ℕ, |c (k + 1)|
  have hsumc : Summable (fun k : ℕ => |c (k + 1)|) := hsum
  have hupper (i : ℕ) (t : Finset ℕ) (ht : ∀ j ∈ t, i < j) :
      ∑ j ∈ t, cov[Y i, Y j; P] ≤ C := by
    calc
      ∑ j ∈ t, cov[Y i, Y j; P] ≤ ∑ j ∈ t, |c ((j - i - 1) + 1)| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [hcov i j (Nat.le_of_lt (ht j hj))]
        have he : j - i = (j - i - 1) + 1 := by have := ht j hj; omega
        rw [he]
        exact le_abs_self _
      _ = ∑ k ∈ t.image (fun j => j - i - 1), |c (k + 1)| := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        dsimp only at hab
        have := ht a ha
        have := ht b hb
        omega
      _ ≤ C := hsumc.sum_le_tsum _ (fun k _ => abs_nonneg _)
  have hlower (i : ℕ) (t : Finset ℕ) (ht : ∀ j ∈ t, j < i) :
      ∑ j ∈ t, cov[Y i, Y j; P] ≤ C := by
    calc
      ∑ j ∈ t, cov[Y i, Y j; P] ≤ ∑ j ∈ t, |c ((i - j - 1) + 1)| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [covariance_comm (Y i) (Y j), hcov j i (Nat.le_of_lt (ht j hj))]
        have he : i - j = (i - j - 1) + 1 := by have := ht j hj; omega
        rw [he]
        exact le_abs_self _
      _ = ∑ k ∈ t.image (fun j => i - j - 1), |c (k + 1)| := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        dsimp only at hab
        have := ht a ha
        have := ht b hb
        omega
      _ ≤ C := hsumc.sum_le_tsum _ (fun k _ => abs_nonneg _)
  have hrow (i : ℕ) (hi : i ∈ s) :
      ∑ j ∈ s, cov[Y i, Y j; P] ≤ c 0 + 2 * C := by
    have hlo := hlower i ((s.erase i).filter (fun j => j < i))
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hhi := hupper i ((s.erase i).filter (fun j => ¬ j < i)) (by
      intro j hj
      obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
      have hne := (Finset.mem_erase.mp hj).1
      omega)
    have hsplit := Finset.sum_filter_add_sum_filter_not (s.erase i)
      (fun j => j < i) (fun j => cov[Y i, Y j; P])
    have hdiag : cov[Y i, Y i; P] = c 0 := by simpa using hcov i i le_rfl
    have herase := Finset.sum_erase_add s (fun j => cov[Y i, Y j; P]) hi
    rw [hdiag] at herase
    linarith
  have hvariance : Var[∑ i ∈ s, Y i; P] = ∑ i ∈ s, ∑ j ∈ s, cov[Y i, Y j; P] :=
    variance_sum' (fun i _ => hmemLp i)
  have hc0 : c 0 = ∫ ω, (Y 0 ω) ^ 2 ∂P := by
    simp only [hc, pow_two]
  calc
    Var[∑ i ∈ s, Y i; P] = ∑ i ∈ s, ∑ j ∈ s, cov[Y i, Y j; P] := hvariance
    _ ≤ ∑ _i ∈ s, (c 0 + 2 * C) := Finset.sum_le_sum hrow
    _ = (s.card : ℝ) * (c 0 + 2 * C) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hc0]

end NumberBoundedPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov


namespace NumberBoundedPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha

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
      exact _root_.NumberBoundedPort_MarkovChainCLT_stationary_mean_transfer.solution P Y hY hstat hcent (k + 1)
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
          exact _root_.NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0 U' V'
            hU'past hV'fut _ (abs_nonneg _) hU'b hV'b
  -- Comparison with the summable α series.
  have hsum : Summable (fun k : ℕ => 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1)) :=
    ((summable_nat_add_iff 1).2 hα).mul_left _
  exact Summable.of_norm_bounded hsum fun k => by simpa using hkey k

end NumberBoundedPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha


namespace NumberBoundedPort_MarkovChainCLT_tendsto_nat_mul_alphaMixingCoef_of_summable

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Abel–Pringsheim: a nonnegative, nonincreasing, summable sequence satisfies
`n * a n → 0`. -/
private theorem tendsto_nat_mul_of_antitone_of_summable' {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hanti : Antitone a) (hsum : Summable a) :
    Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0) := by
  have key : ∀ n : ℕ, (n : ℝ) * a n ≤ 2 * ∑' k : ℕ, a (k + n / 2) := by
    intro n
    have hsub : ((n - n / 2 : ℕ) : ℝ) * a n ≤ ∑ k ∈ Finset.Ico (n / 2) n, a k := by
      have hmono : ∀ k ∈ Finset.Ico (n / 2) n, a n ≤ a k :=
        fun k hk => hanti (Finset.mem_Ico.1 hk).2.le
      calc ((n - n / 2 : ℕ) : ℝ)
            * a n = ∑ _k ∈ Finset.Ico (n / 2) n, a n := by
              rw [Finset.sum_const, Nat.card_Ico]
              simp [mul_comm]
        _ ≤ ∑ k ∈ Finset.Ico (n / 2) n, a k := Finset.sum_le_sum hmono
    have htail : ∑ k ∈ Finset.Ico (n / 2) n, a k ≤ ∑' k : ℕ, a (k + n / 2) := by
      have hs : Summable fun k : ℕ => a (k + n / 2) := hsum.comp_injective (add_left_injective _)
      have hmap : ∑ k ∈ Finset.Ico (n / 2) n, a k
          = ∑ k ∈ Finset.range (n - n / 2), a (k + n / 2) := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
        simp [add_comm]
      rw [hmap]
      exact hs.sum_le_tsum _ fun k _ => ha0 _
    have hhalf : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
      have h : n ≤ 2 * (n - n / 2) := by omega
      exact_mod_cast h
    calc (n : ℝ) * a n ≤ (2 * ((n - n / 2 : ℕ) : ℝ)) * a n :=
          mul_le_mul_of_nonneg_right hhalf (ha0 n)
      _ = 2 * (((n - n / 2 : ℕ) : ℝ) * a n) := by ring
      _ ≤ 2 * ∑ k ∈ Finset.Ico (n / 2) n, a k := by linarith
      _ ≤ 2 * ∑' k : ℕ, a (k + n / 2) := by linarith
  have hzero : Tendsto (fun j : ℕ => ∑' k : ℕ, a (k + j)) atTop (𝓝 0) := tendsto_sum_nat_add a
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
  have hcomp : Tendsto (fun n : ℕ => 2 * ∑' k : ℕ, a (k + n / 2)) atTop (𝓝 0) := by
    simpa using (hzero.comp hdiv).const_mul (2 : ℝ)
  exact squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n) (ha0 n)) key hcomp

theorem solution {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hα : Summable fun n => alphaMixingCoef P Y n) :
    Tendsto (fun n : ℕ => (n : ℝ) * alphaMixingCoef P Y n) atTop (𝓝 0) := by
  have hα_nonneg : ∀ n : ℕ, 0 ≤ alphaMixingCoef P Y n := by
    intro n
    refine le_csSup ⟨1, ?_⟩
      ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
        @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
    rintro r ⟨k, A, B, -, -, rfl⟩
    have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ (A ∩ B)))
    have hA1 : (P A).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ A))
    have hB1 : (P B).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ B))
    have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
    have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
    have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> nlinarith
  exact tendsto_nat_mul_of_antitone_of_summable' hα_nonneg
    (_root_.NumberBoundedPort_MarkovChainCLT_alphaMixingCoef_antitone.solution P Y) hα

end NumberBoundedPort_MarkovChainCLT_tendsto_nat_mul_alphaMixingCoef_of_summable


namespace NumberBoundedPort_MarkovChainCLT_tendsto_integral_pow_four_partialSum_div_cube_of_bounded_of_summable_alpha

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FourthMomentSubcubicAux

private def fourEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun v := (v 0, v 1, v 2, v 3)
  invFun v := ![v.1, v.2.1, v.2.2.1, v.2.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by rcases v with ⟨a,b,c,d⟩; rfl

private lemma sum_four {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    ∑ v, f v = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  rw [Fintype.sum_equiv (fourEquiv α) f
    (fun p => f ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun v => by
      congr 1; ext i; fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type]

private lemma sum_le_twentyfour_ordered {n : ℕ}
    (F : (Fin 4 → Fin n) → ℝ) (hF : ∀ v, 0 ≤ F v)
    (hperm : ∀ v (σ : Equiv.Perm (Fin 4)), F (v ∘ σ) = F v) :
    ∑ v, F v ≤ 24 * ∑ v, if Monotone v then F v else 0 := by
  classical
  have hp (v : Fin 4 → Fin n) :
      F v ≤ ∑ σ : Equiv.Perm (Fin 4), if Monotone (v ∘ σ) then F (v ∘ σ) else 0 := by
    calc
      F v = if Monotone (v ∘ Tuple.sort v) then F (v ∘ Tuple.sort v) else 0 := by
        rw [if_pos (Tuple.monotone_sort v), hperm]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (a := Tuple.sort v)
        (f := fun σ : Equiv.Perm (Fin 4) => if Monotone (v ∘ σ) then F (v ∘ σ) else 0)
        (fun σ _ => by split_ifs; exact hF _; exact le_rfl) (Finset.mem_univ _)
  have hb (σ : Equiv.Perm (Fin 4)) : Function.Bijective (fun v : Fin 4 → Fin n => v ∘ σ) := by
    constructor
    · intro v w hvw
      funext i
      have h := congrFun hvw (σ.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
    · intro v
      refine ⟨v ∘ σ.symm, ?_⟩
      ext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hr (σ : Equiv.Perm (Fin 4)) :
      (∑ v : Fin 4 → Fin n, if Monotone (v ∘ σ) then F (v ∘ σ) else 0) =
        ∑ v : Fin 4 → Fin n, if Monotone v then F v else 0 :=
    (hb σ).sum_comp (fun v => if Monotone v then F v else 0)
  calc
    ∑ v, F v ≤ ∑ v, ∑ σ : Equiv.Perm (Fin 4),
        if Monotone (v ∘ σ) then F (v ∘ σ) else 0 := Finset.sum_le_sum (fun v _ => hp v)
    _ = ∑ σ : Equiv.Perm (Fin 4), ∑ v : Fin 4 → Fin n,
        if Monotone (v ∘ σ) then F (v ∘ σ) else 0 := Finset.sum_comm
    _ = 24 * ∑ v, if Monotone v then F v else 0 := by
      simp_rw [hr]
      norm_num [Fintype.card_perm]

private lemma shift_sum_le {n : ℕ} (i : Fin n) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ j : Fin n, if i ≤ j then f (j.val-i.val) else 0) ≤ ∑ k ∈ Finset.range n, f k := by
  classical
  let s := Finset.univ.filter (fun j : Fin n => i ≤ j)
  calc
    _ = ∑ j ∈ s, f (j.val-i.val) := by rw [Finset.sum_filter]
    _ = ∑ k ∈ s.image (fun j => j.val-i.val), f k := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      dsimp only at hab
      apply Fin.ext; omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro k hk; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr ((Nat.sub_le _ _).trans_lt j.isLt)) (by intros; exact hf _)

private lemma gap_sum_bound (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (n : ℕ) :
    (∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, A (max r s)) ≤
      2 * ∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k := by
  classical
  have hrow (k : ℕ) (hk : k < n) :
      (∑ r ∈ Finset.range n, if r ≤ k then A k else 0) = ((k:ℝ)+1)*A k := by
    rw [← Finset.sum_filter]
    have he : (Finset.range n).filter (fun r => r ≤ k) = Finset.range (k+1) := by
      ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [he]; simp
  have hpt (r s : ℕ) : A (max r s) ≤
      (if r ≤ s then A s else 0) + (if s ≤ r then A r else 0) := by
    rcases le_total r s with h | h
    · rw [max_eq_right h, if_pos h]; split_ifs <;> linarith [hA r]
    · rw [max_eq_left h, if_pos h]; split_ifs <;> linarith [hA s]
  calc
    _ ≤ ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n,
        ((if r ≤ s then A s else 0) + (if s ≤ r then A r else 0)) :=
      Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs => hpt r s
    _ = (∑ s ∈ Finset.range n, ∑ r ∈ Finset.range n, if r ≤ s then A s else 0) +
        ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, if s ≤ r then A r else 0 := by
      simp only [Finset.sum_add_distrib]; rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [Finset.sum_congr rfl (fun k hk => hrow k (Finset.mem_range.mp hk))]
      ring

private lemma fourth_sum_bound {n : ℕ} (F : (Fin 4 → Fin n) → ℝ)
    (hF : ∀ v, 0 ≤ F v)
    (hperm : ∀ v (σ : Equiv.Perm (Fin 4)), F (v ∘ σ) = F v)
    (D : ℝ) (hD : 0 ≤ D) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (hord : ∀ v, Monotone v → F v ≤ D*A (max ((v 1).val-(v 0).val) ((v 3).val-(v 2).val))) :
    ∑ v, F v ≤ 48*D*(n:ℝ)^2 * (∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k) := by
  classical
  let Q (i j k l : Fin n) : ℝ := if i ≤ j then
    if k ≤ l then A (max (j.val-i.val) (l.val-k.val)) else 0 else 0
  have hQ (i j k l : Fin n) : 0 ≤ Q i j k l := by dsimp [Q]; split_ifs <;> first | exact hA _ | positivity
  have hterm (v : Fin 4 → Fin n) : (if Monotone v then F v else 0) ≤ D*Q (v 0) (v 1) (v 2) (v 3) := by
    split_ifs with hv
    · simpa only [Q, if_pos (hv (by decide : (0:Fin 4) ≤ 1)),
        if_pos (hv (by decide : (2:Fin 4) ≤ 3))] using hord v hv
    · exact mul_nonneg hD (hQ _ _ _ _)
  have hrow (i k : Fin n) : (∑ j : Fin n, ∑ l : Fin n, Q i j k l) ≤
      ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, A (max r s) := by
    calc
      _ ≤ ∑ j : Fin n, if i ≤ j then ∑ s ∈ Finset.range n, A (max (j.val-i.val) s) else 0 := by
        apply Finset.sum_le_sum; intro j hj
        by_cases hij : i ≤ j
        · simp only [Q, if_pos hij]
          exact shift_sum_le k (fun s => A (max (j.val-i.val) s)) (fun s => hA _)
        · simp [Q, hij]
      _ ≤ _ := shift_sum_le i _ (fun r => Finset.sum_nonneg fun s hs => hA _)
  have hsumQ : (∑ v : Fin 4 → Fin n, Q (v 0) (v 1) (v 2) (v 3)) ≤
      (n:ℝ)^2 * (2 * ∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k) := by
    rw [sum_four]
    change (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, Q i j k l) ≤ _
    calc
      _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n, Q i j k l := by
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]
      _ ≤ ∑ i : Fin n, ∑ k : Fin n, (2 * ∑ r ∈ Finset.range n, ((r:ℝ)+1)*A r) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => (hrow i k).trans (gap_sum_bound A hA n)
      _ = _ := by simp; ring
  calc
    ∑ v, F v ≤ 24 * ∑ v, if Monotone v then F v else 0 := sum_le_twentyfour_ordered F hF hperm
    _ ≤ 24 * ∑ v, D*Q (v 0) (v 1) (v 2) (v 3) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hterm v) (by norm_num)
    _ = 24*D*(∑ v : Fin 4 → Fin n, Q (v 0) (v 1) (v 2) (v 3)) := by rw [← Finset.mul_sum]; ring
    _ ≤ 24*D*((n:ℝ)^2 * (2 * ∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k)) :=
      mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ = _ := by ring

private lemma weighted_sum_div_tendsto_zero {A : ℕ → ℝ} (hA : Summable A) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k) / n) atTop (𝓝 0) := by
  have hid (n : ℕ) : (∑ k ∈ Finset.range n, ((k:ℝ)+1)*A k) =
      (n:ℝ)*(∑ k ∈ Finset.range n, A k) - ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range j, A k := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]; rw [ih]; ring
  have hsum := hA.hasSum.tendsto_sum_nat
  have h := hsum.sub hsum.cesaro
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hid]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

private lemma coord_measurable {Ω : Type*} (X : ℕ → Ω → ℝ)
    (s : Set ℕ) (i : ℕ) (hi : i ∈ s) : Measurable[processSigma X s] (X i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

private lemma mean_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hs : IsStrictlyStationary P X) (hc : ∫ ω, X 0 ω ∂P = 0) (i : ℕ) :
    ∫ ω, X i ω ∂P = 0 := by
  have hmap : P.map (X i) = P.map (X 0) := by
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hs i)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hX (n+i)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hX n)] at h
    simpa [Function.comp_def] using h
  have h1 : ∫ x, x ∂(P.map (X i)) = ∫ ω, X i ω ∂P :=
    integral_map (hX i).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  have h0 : ∫ x, x ∂(P.map (X 0)) = ∫ ω, X 0 ω ∂P :=
    integral_map (hX 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  rw [← h1, hmap, h0, hc]

private lemma ordered_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (B : ℝ) (hB : 1 ≤ B) (hXB : ∀ i ω, |X i ω| ≤ B)
    (i j k l : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤
      (4 * (B^3)^2) * alphaMixingCoef P X (max (j-i) (l-k)) := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hB3 : B ≤ B^3 := by
    have hsq : 1 ≤ B^2 := one_le_pow₀ hB
    nlinarith [mul_le_mul_of_nonneg_left hsq hB0]
  have hmem (i : ℕ) : MemLp (X i) 2 P := MemLp.of_bound
    (hX i).aestronglyMeasurable B (ae_of_all _ fun ω => by simpa using hXB i ω)
  have hb3 (i j k : ℕ) (ω : Ω) : |X i ω * X j ω * X k ω| ≤ B^3 := by
    simp only [abs_mul]
    calc
      |X i ω| * |X j ω| * |X k ω| ≤ B*B*B := by gcongr <;> exact hXB _ _
      _ = B^3 := by ring
  have hmem3 (i j k : ℕ) : MemLp (fun ω => X i ω * X j ω * X k ω) 2 P :=
    MemLp.of_bound (by fun_prop) (B^3) (ae_of_all _ fun ω => by simpa using hb3 i j k ω)
  let D : ℝ := 4 * (B^3)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hleft : |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤ D*alphaMixingCoef P X (j-i) := by
    have hcov := _root_.NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded.solution P X hX (j-i) i (X i)
      (fun ω => X j ω * X k ω * X l ω)
      (coord_measurable X (Set.Iic i) i (by simp))
      (((coord_measurable X (Set.Ici (i+(j-i))) j (by simp only [Set.mem_Ici]; omega)).mul
        (coord_measurable X (Set.Ici (i+(j-i))) k (by simp only [Set.mem_Ici]; omega))).mul
        (coord_measurable X (Set.Ici (i+(j-i))) l (by simp only [Set.mem_Ici]; omega)))
      (B^3) (by positivity) (fun ω => (hXB i ω).trans hB3) (hb3 j k l)
    rw [covariance_eq_sub (hmem i) (hmem3 j k l), hmean i, zero_mul, sub_zero] at hcov
    have he : (∫ ω, X i ω * X j ω * X k ω * X l ω ∂P) =
        ∫ ω, (X i * (fun ω => X j ω * X k ω * X l ω)) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [Pi.mul_apply]
      ring
    rw [he]
    exact hcov
  have hright : |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤ D*alphaMixingCoef P X (l-k) := by
    have hcov := _root_.NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded.solution P X hX (l-k) k
      (fun ω => X i ω * X j ω * X k ω) (X l)
      (((coord_measurable X (Set.Iic k) i (by simp only [Set.mem_Iic]; omega)).mul
        (coord_measurable X (Set.Iic k) j hjk)).mul (coord_measurable X (Set.Iic k) k (by simp)))
      (coord_measurable X (Set.Ici (k+(l-k))) l (by simp only [Set.mem_Ici]; omega))
      (B^3) (by positivity) (hb3 i j k) (fun ω => (hXB l ω).trans hB3)
    rw [covariance_eq_sub (hmem3 i j k) (hmem l), hmean l, mul_zero, sub_zero] at hcov
    exact hcov
  rcases le_total (j-i) (l-k) with h | h
  · simpa only [max_eq_right h] using hright
  · simpa only [max_eq_left h] using hleft

private theorem pointwise_fourth_subcubic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hstat : IsStrictlyStationary P X)
    (hcent : ∫ ω, X 0 ω ∂P = 0)
    (M : ℝ) (hM : ∀ i, ∀ ω, |X i ω| ≤ M)
    (hα : Summable (alphaMixingCoef P X)) :
    Tendsto (fun n : ℕ => (∫ ω, (∑ i ∈ Finset.range n, X i ω)^4 ∂P) / (n:ℝ)^3)
      atTop (𝓝 0) := by
  classical
  let B : ℝ := 1+|M|
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg M]
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hXB (i : ℕ) (ω : Ω) : |X i ω| ≤ B :=
    (hM i ω).trans (by dsimp [B]; linarith [le_abs_self M])
  let D : ℝ := 4*(B^3)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA (k : ℕ) : 0 ≤ alphaMixingCoef P X k := by
    apply Real.sSup_nonneg
    rintro r ⟨k,A,B,hA,hB,rfl⟩
    exact abs_nonneg _
  have hbound (n : ℕ) :
      ∫ ω, (∑ i ∈ Finset.range n, X i ω)^4 ∂P ≤
        48*D*(n:ℝ)^2 * (∑ k ∈ Finset.range n, ((k:ℝ)+1)*alphaMixingCoef P X k) := by
    let H (v : Fin 4 → Fin n) (ω : Ω) : ℝ := ∏ q : Fin 4, X (v q).val ω
    have hHm (v : Fin 4 → Fin n) : Measurable (H v) := by dsimp [H]; fun_prop
    have hHint (v : Fin 4 → Fin n) : Integrable (H v) P := by
      have hbound (ω : Ω) : ‖H v ω‖ ≤ B^4 := by
        dsimp [H]
        rw [Finset.abs_prod]
        calc
          ∏ q : Fin 4, |X (v q).val ω| ≤ ∏ _q : Fin 4, B :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun q _ => hXB _ _)
          _ = B^4 := by simp
      exact (MemLp.of_bound (hHm v).aestronglyMeasurable (B^4)
        (ae_of_all _ hbound) : MemLp (H v) 2 P).integrable (by norm_num)
    let F (v : Fin 4 → Fin n) : ℝ := |∫ ω, H v ω ∂P|
    have hF (v : Fin 4 → Fin n) : 0 ≤ F v := abs_nonneg _
    have hperm (v : Fin 4 → Fin n) (σ : Equiv.Perm (Fin 4)) : F (v ∘ σ) = F v := by
      dsimp [F]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ω
      exact Equiv.prod_comp σ (fun q => X (v q).val ω)
    have hord (v : Fin 4 → Fin n) (hv : Monotone v) :
        F v ≤ D*alphaMixingCoef P X (max ((v 1).val-(v 0).val) ((v 3).val-(v 2).val)) := by
      have h := ordered_product_bound P X hX (mean_coord P X hX hstat hcent)
        B hB hXB (v 0).val (v 1).val (v 2).val (v 3).val
        (hv (by decide : (0 : Fin 4) ≤ 1)) (hv (by decide : (1 : Fin 4) ≤ 2))
        (hv (by decide : (2 : Fin 4) ≤ 3))
      simpa only [F, H, Fin.prod_univ_four, D] using h
    have hexp (ω : Ω) : (∑ i ∈ Finset.range n, X i ω)^4 =
        ∑ v : Fin 4 → Fin n, H v ω := by
      rw [Finset.sum_range]
      have h := Fintype.prod_sum (fun (_q : Fin 4) (i : Fin n) => X i.val ω)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, H] using h
    calc
      (∫ ω, (∑ i ∈ Finset.range n, X i ω)^4 ∂P) = ∑ v : Fin 4 → Fin n, ∫ ω, H v ω ∂P := by
        simp_rw [hexp]
        exact integral_finsetSum _ (fun v _ => hHint v)
      _ ≤ ∑ v : Fin 4 → Fin n, F v := Finset.sum_le_sum (fun v _ => le_abs_self _)
      _ ≤ _ := fourth_sum_bound F hF hperm D hD (alphaMixingCoef P X) hA hord
  have hlim := (weighted_sum_div_tendsto_zero hα).const_mul (48*D)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => div_nonneg
    (integral_nonneg fun ω => by positivity) (by positivity)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    _ ≤ (48*D*(n:ℝ)^2 * (∑ k ∈ Finset.range n, ((k:ℝ)+1)*alphaMixingCoef P X k)) / (n:ℝ)^3 :=
      div_le_div_of_nonneg_right (hbound n) (by positivity)
    _ = _ := by field_simp


end FourthMomentSubcubicAux

open FourthMomentSubcubicAux in
/-- Ibragimov–Linnik, Lemma 18.5.2: bounded summably mixing sums have subcubic fourth moment. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Tendsto (fun n : ℕ => (∫ ω, (∑ i ∈ Finset.range n, Y i ω)^4 ∂P) / (n:ℝ)^3)
      atTop (𝓝 0) := by
  let K : ℝ := 1+|B|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let f : ℝ → ℝ := fun x => max (-K) (min K x)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hfb (x : ℝ) : |f x| ≤ K := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let Z : ℕ → Ω → ℝ := fun i ω => f (Y i ω)
  have hZeq (i : ℕ) : Z i =ᵐ[P] Y i := (hB i).mono fun ω hω => by
    dsimp [Z,f]
    have hb : |Y i ω| ≤ K := hω.le.trans (by dsimp [K]; linarith [le_abs_self B])
    rw [min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  have hZm (i : ℕ) : Measurable (Z i) := hf.comp (hY i)
  have hZstat : IsStrictlyStationary P Z := isStrictlyStationary_comp_of_measurable P Y hY hstat f hf
  have hZcent : ∫ ω, Z 0 ω ∂P = 0 := (integral_congr_ae (hZeq 0)).trans hcent
  have hZa (i : ℕ) : 0 ≤ alphaMixingCoef P Z i ∧ alphaMixingCoef P Z i ≤ alphaMixingCoef P Y i :=
    alphaMixingCoef_comp_nonneg_le_of_finite P Y f hf i
  have hZsum : Summable (alphaMixingCoef P Z) :=
    Summable.of_nonneg_of_le (fun i => (hZa i).1) (fun i => (hZa i).2) hα
  have h := pointwise_fourth_subcubic P Z hZm hZstat hZcent K (fun i ω => hfb _) hZsum
  apply h.congr
  intro n
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hZeq] with ω hω
  simp only [hω]

end NumberBoundedPort_MarkovChainCLT_tendsto_integral_pow_four_partialSum_div_cube_of_bounded_of_summable_alpha


namespace NumberBoundedPort_MarkovChainCLT_exists_independent_blocks_of_bounded_of_summable_alpha

set_option autoImplicit false

open Filter
open scoped Topology

namespace AdaptiveBlockAux

lemma exists_slow_growth {γ : ℕ → ℝ} (hγ : Tendsto γ atTop (𝓝 0)) :
    ∃ h : ℕ → ℕ, (∀ q, 1 ≤ h q) ∧ Tendsto h atTop atTop ∧
      ∀ᶠ q in atTop, (h q)^4 ≤ q ∧ ∀ r ≥ q, γ r ≤ 1/(h q:ℝ)^4 := by
  classical
  let P : ℕ → ℕ → Prop := fun q k => (k+1)^4 ≤ q ∧ ∀ r ≥ q, γ r ≤ 1/((k+1:ℕ):ℝ)^4
  have he (k : ℕ) : ∀ᶠ q in atTop, P q k := by
    have hc : 0 < 1/((k+1:ℕ):ℝ)^4 := by positivity
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hγ.eventually_lt_const hc)
    filter_upwards [eventually_ge_atTop (max N ((k+1)^4))] with q hq
    exact ⟨(le_max_right _ _).trans hq, fun r hr => (hN r ((le_max_left _ _).trans (hq.trans hr))).le⟩
  let h : ℕ → ℕ := fun q => Nat.findGreatest (P q) q + 1
  refine ⟨h, fun q => by dsimp [h]; omega, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro k
    filter_upwards [he k, eventually_ge_atTop k] with q hq hkq
    have hh := Nat.le_findGreatest hkq hq
    dsimp [h]; omega
  · filter_upwards [he 0] with q hq
    exact Nat.findGreatest_spec (Nat.zero_le q) hq

lemma sqrt_tendsto : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (k*k)] with n hn
  exact (Nat.le_sqrt).mpr hn

lemma exists_schedule {γ : ℕ → ℝ} (hγ : Tendsto γ atTop (𝓝 0))
    (hγpos : ∀ r, 0 ≤ γ r) :
    ∃ p q : ℕ → ℕ,
      (∀ n, 0 < p n) ∧ Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      Tendsto (fun n => (p n:ℝ)/n) atTop (𝓝 0) ∧
      Tendsto (fun n => ((n-n/(p n+q n)*p n:ℕ):ℝ)/n) atTop (𝓝 0) ∧
      Tendsto (fun n => γ (p n)*(p n:ℝ)^2/n) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, (n:ℝ)/(p n:ℝ) ≤ 4*(q n:ℝ)) := by
  obtain ⟨h,hh,hht,hgood⟩ := exists_slow_growth hγ
  let q : ℕ → ℕ := fun n => max 1 (Nat.sqrt n)
  let p : ℕ → ℕ := fun n => h (q n)*q n
  have hqpos (n : ℕ) : 0 < q n := by dsimp [q]; omega
  have hpq (n : ℕ) : q n ≤ p n := by
    dsimp [p]; simpa using Nat.mul_le_mul_right (q n) (hh (q n))
  have hqt : Tendsto q atTop atTop := tendsto_atTop_mono (fun n => le_max_right 1 (Nat.sqrt n)) sqrt_tendsto
  have hpt : Tendsto p atTop atTop := tendsto_atTop_mono hpq hqt
  have hht' := hht.comp hqt
  have hhi : Tendsto (fun n => (h (q n):ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hht')
  have hg : ∀ᶠ n in atTop,
      (q n)^2 ≤ n ∧ n < (q n+1)^2 ∧ (h (q n))^4 ≤ q n ∧
        ∀ r ≥ q n, γ r ≤ 1/(h (q n):ℝ)^4 := by
    filter_upwards [hqt.eventually hgood, eventually_ge_atTop 1] with n hn hn1
    have hqs : q n = Nat.sqrt n := by
      apply max_eq_right
      exact Nat.le_sqrt.mpr (by simpa using hn1)
    exact ⟨by rw [hqs]; exact by simpa [pow_two] using Nat.sqrt_le n,
      by rw [hqs]; simpa [pow_two] using Nat.lt_succ_sqrt n, hn⟩
  have hpratio : ∀ᶠ n in atTop, (p n:ℝ)/n ≤ (h (q n):ℝ)⁻¹ := by
    filter_upwards [hg] with n ⟨hqn,_,hhq,_⟩
    have hQ : (0:ℝ) < q n := by exact_mod_cast hqpos n
    have hH : (1:ℝ) ≤ h (q n) := by exact_mod_cast hh (q n)
    have hQn : (q n:ℝ)^2 ≤ n := by exact_mod_cast hqn
    have hHq : (h (q n):ℝ)^4 ≤ q n := by exact_mod_cast hhq
    have hH2 : (h (q n):ℝ)^2 ≤ q n := by
      nlinarith [sq_nonneg ((h (q n):ℝ)^2-1)]
    have hN : (0:ℝ) < n := lt_of_lt_of_le (sq_pos_of_pos hQ) hQn
    dsimp [p]; push_cast
    rw [← one_div, div_le_div_iff₀ hN (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hH2 hQ.le]
  have hpr : Tendsto (fun n => (p n:ℝ)/n) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => by positivity) hpratio hhi
  have hqr : Tendsto (fun n => (q n:ℝ)/n) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity) (fun n => by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hpq n) (by positivity)) hpr
  have hLr : Tendsto (fun n => ((p n+q n:ℕ):ℝ)/n) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, add_div, zero_add] using hpr.add hqr
  have hdr : Tendsto (fun n => ((n-n/(p n+q n)*p n:ℕ):ℝ)/n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ (by
      simpa using hLr.add hhi)
    filter_upwards [eventually_ge_atTop 1] with n hn
    let m := n/(p n+q n)
    have hmp : m*p n ≤ n := (Nat.mul_le_mul_left m (Nat.le_add_right _ _)).trans (Nat.div_mul_le_self _ _)
    have hrem : n < (m+1)*(p n+q n) := by
      simpa [m, mul_comm] using Nat.lt_mul_div_succ n (show 0 < p n+q n by have := hqpos n; omega)
    have hN : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hH : (0:ℝ) < h (q n) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hh _))
    have hmpR : (m:ℝ)*(p n:ℝ) ≤ n := by exact_mod_cast hmp
    have hremR : (n:ℝ) < ((m:ℝ)+1)*((p n:ℝ)+q n) := by exact_mod_cast hrem
    change ((n-m*p n:ℕ):ℝ)/n ≤ _
    rw [Nat.cast_sub hmp, Nat.cast_mul]
    field_simp
    have hremH := mul_le_mul_of_nonneg_right hremR.le hH.le
    dsimp [p] at *; push_cast at *
    nlinarith
  have hfour : Tendsto (fun n => γ (p n)*(p n:ℝ)^2/n) atTop (𝓝 0) := by
    have hhi2 := hhi.pow 2
    simp only [zero_pow (by decide : 2≠0)] at hhi2
    apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg
      (mul_nonneg (hγpos _) (sq_nonneg _)) (by positivity)) _ hhi2
    filter_upwards [hg] with n ⟨hqn,_,_,hγn⟩
    have hQ : (0:ℝ) < q n := by exact_mod_cast hqpos n
    have hH : (0:ℝ) < h (q n) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hh _))
    have hQn : (q n:ℝ)^2 ≤ n := by exact_mod_cast hqn
    have hN : (0:ℝ) < n := lt_of_lt_of_le (sq_pos_of_pos hQ) hQn
    have hgP := hγn (p n) (hpq n)
    calc
      _ ≤ (1/(h (q n):ℝ)^4)*(p n:ℝ)^2/n := by gcongr
      _ ≤ (h (q n):ℝ)⁻¹^2 := by
        dsimp [p]; push_cast
        field_simp
        nlinarith [mul_le_mul_of_nonneg_left hQn (sq_nonneg (h (q n):ℝ))]
  refine ⟨p,q,fun n => (hqpos n).trans_le (hpq n),hpt,hqt,hpr,hdr,hfour,?_⟩
  filter_upwards [hg] with n ⟨_,hn,_,_⟩
  have hQ : (1:ℝ) ≤ q n := by exact_mod_cast hqpos n
  have hP : (0:ℝ) < p n := by exact_mod_cast (hqpos n).trans_le (hpq n)
  have hPQ : (q n:ℝ) ≤ p n := by exact_mod_cast hpq n
  have hN : (n:ℝ) < ((q n:ℝ)+1)^2 := by exact_mod_cast hn
  rw [div_le_iff₀ hP]
  nlinarith

end AdaptiveBlockAux

open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace IndependentArrayAux

lemma exp_remainder_two (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x‖ ≤ |x|^2 := by
  let f : ℝ → ℂ := fun y => Complex.exp (I*y) - 1 - I*y
  have hd (y : ℝ) : HasDerivAt f (I*(Complex.exp (I*y)-1)) y := by
    have h : HasDerivAt (fun y : ℝ => I*(y:ℂ)) I y := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul I
    convert (h.cexp.sub_const 1).sub h using 1 <;> first | rfl | ring
  have hb (y : ℝ) (hy : y ∈ Set.Icc (-|x|) |x|) :
      ‖I*(Complex.exp (I*y)-1)‖ ≤ |x| := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y)).trans (by
        rw [Real.norm_eq_abs]; exact abs_le.mpr hy)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hb (convex_Icc (-|x|) |x|)
    (show (0:ℝ) ∈ Set.Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simpa [f, Real.norm_eq_abs, pow_two] using h

lemma exp_remainder_three (x : ℝ) :
    ‖Complex.exp (I*x) - 1 - I*x + (x:ℂ)^2/2‖ ≤ |x|^3 := by
  let f : ℝ → ℂ := fun y => Complex.exp (I*y) - 1 - I*y + (y:ℂ)^2/2
  have hd (y : ℝ) : HasDerivAt f (I*(Complex.exp (I*y)-1-I*y)) y := by
    have h : HasDerivAt (fun y : ℝ => I*(y:ℂ)) I y := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul I
    convert ((h.cexp.sub_const 1).sub h).add
      ((Complex.ofRealCLM.hasDerivAt.pow 2).div_const 2) using 1
    all_goals first | rfl | skip
    all_goals try simp only [Nat.cast_ofNat, pow_one, mul_one, Complex.ofRealCLM_apply, Complex.ofReal_one, Nat.reduceSub]
    linear_combination -(y:ℂ) * Complex.I_sq
  have hb (y : ℝ) (hy : y ∈ Set.Icc (-|x|) |x|) :
      ‖I*(Complex.exp (I*y)-1-I*y)‖ ≤ |x|^2 := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (exp_remainder_two y).trans (pow_le_pow_left₀ (abs_nonneg y) (abs_le.mpr hy) 2)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hb (convex_Icc (-|x|) |x|)
    (show (0:ℝ) ∈ Set.Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simpa [f, Real.norm_eq_abs, pow_succ] using h

lemma tendsto_pow_of_scaled_sub {z : ℕ → ℂ} {m : ℕ → ℕ} {a : ℂ}
    (hz : Tendsto z atTop (𝓝 1))
    (ha : Tendsto (fun n => (m n : ℂ)*(z n-1)) atTop (𝓝 a)) :
    Tendsto (fun n => z n ^ m n) atTop (𝓝 (Complex.exp a)) := by
  have hw : Tendsto (fun n => z n-1) atTop (𝓝 0) := by simpa using hz.sub_const 1
  have hb := Complex.log_sub_self_isBigO.comp_tendsto hw
  have ho : (fun n => (m n:ℂ)*(Complex.log (1+(z n-1))-(z n-1)))
      =O[atTop] (fun n => (m n:ℂ)*(z n-1)^2) := (Asymptotics.isBigO_refl _ _).mul hb
  have hzero : Tendsto (fun n => (m n:ℂ)*(z n-1)^2) atTop (𝓝 0) := by
    simpa only [mul_zero, pow_two, mul_assoc] using ha.mul hw
  have he := ho.trans_tendsto hzero
  have hl : Tendsto (fun n => (m n:ℂ)*Complex.log (z n)) atTop (𝓝 a) := by
    simpa only [show ∀ w:ℂ, 1+(w-1)=w by intro w; ring, mul_sub, sub_add_cancel, zero_add] using he.add ha
  have hne : ∀ᶠ n in atTop, z n ≠ 0 := hz.eventually_ne (by norm_num)
  apply (Complex.continuous_exp.tendsto a |>.comp hl).congr'
  filter_upwards [hne] with n hn
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log hn]

end IndependentArrayAux

open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IndependentArrayAux

lemma third_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 4 P) :
    (∫ ω, |X ω|^3 ∂P) ≤ Real.sqrt (∫ ω, (X ω)^2 ∂P)*Real.sqrt (∫ ω, (X ω)^4 ∂P) := by
  have h2 : MemLp (fun ω => (X ω)^2) 2 P := by
    have h := hX.norm_rpow_div 2
    have he : (4:ENNReal)/2 = 2 := by
      change ((4:NNReal):ENNReal)/((2:NNReal):ENNReal)=((2:NNReal):ENNReal)
      rw [← ENNReal.coe_div (by norm_num)]
      norm_num
    simpa [he, Real.norm_eq_abs, sq_abs] using h
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (f := fun ω => |X ω|) (g := fun ω => (X ω)^2)
    (ae_of_all _ fun ω => abs_nonneg _) (ae_of_all _ fun ω => sq_nonneg _)
    (by simpa using (hX.mono_exponent (show (2:ENNReal)≤4 by norm_num)).norm) (by simpa using h2)
  simpa only [Real.rpow_two, sq_abs, ← pow_mul, ← Real.sqrt_eq_rpow, show 2*2=4 by rfl,
    show ∀ x:ℝ, |x| * x^2=|x|^3 by intro x; rw [← sq_abs x]; ring] using h

lemma charFun_cubic_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (h4 : MemLp X 4 P) (h0 : ∫ ω, X ω ∂P = 0) (t : ℝ) :
    ‖charFun (P.map X) t - (1 - (t:ℂ)^2*(∫ ω, (X ω)^2 ∂P)/2)‖ ≤
      |t|^3*(∫ ω, |X ω|^3 ∂P) := by
  have hi := h4.integrable (by norm_num)
  have h2 := (h4.mono_exponent (show (2:ENNReal)≤4 by norm_num)).integrable_sq
  have h3 : Integrable (fun ω => |X ω|^3) P := by
    simpa [Real.norm_eq_abs] using (h4.mono_exponent (show (3:ENNReal)≤4 by norm_num)).integrable_norm_pow'
  have he : Integrable (fun ω => Complex.exp (I*((t*X ω:ℝ):ℂ))) P := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop)
    exact ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal (t*X ω)).le
  have hlin : Integrable (fun ω => I*((t*X ω:ℝ):ℂ)) P := (hi.const_mul t).ofReal.const_mul I
  have hquad : Integrable (fun ω => (((t*X ω:ℝ):ℂ)^2)/2) P := by
    simp_rw [Complex.ofReal_mul, mul_pow]
    have h2c : Integrable (fun ω => ((X ω)^2:ℝ)) P := h2
    have h2C : Integrable (fun ω => (((X ω)^2:ℝ):ℂ)) P := h2c.ofReal
    simpa only [Complex.ofReal_pow] using ((h2C.const_mul ((t:ℂ)^2)).div_const 2)
  have hs1 : Integrable (fun ω => Complex.exp (I*((t*X ω:ℝ):ℂ))-1) P := he.sub (integrable_const (1:ℂ))
  have hs2 : Integrable (fun ω => Complex.exp (I*((t*X ω:ℝ):ℂ))-1-I*((t*X ω:ℝ):ℂ)) P := hs1.sub hlin
  have hR := hs2.add hquad
  have heq : charFun (P.map X) t - (1 - (t:ℂ)^2*(∫ ω, (X ω)^2 ∂P)/2) =
      ∫ ω, Complex.exp (I*((t*X ω:ℝ):ℂ))-1-I*((t*X ω:ℝ):ℂ)+((t*X ω:ℝ):ℂ)^2/2 ∂P := by
    rw [integral_add hs2 hquad,
      integral_sub hs1 hlin,
      integral_sub he (integrable_const (1:ℂ))]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_complex_ofReal, h0, mul_zero, Complex.ofReal_zero, sub_zero,
      Complex.ofReal_mul, mul_pow, integral_div, integral_const_mul, ← Complex.ofReal_pow,
      integral_complex_ofReal]
    rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]
    simp only [← Complex.ofReal_mul, mul_comm I]
    ring
  rw [heq]
  calc
    _ ≤ ∫ ω, ‖Complex.exp (I*((t*X ω:ℝ):ℂ))-1-I*((t*X ω:ℝ):ℂ)+((t*X ω:ℝ):ℂ)^2/2‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t|^3*|X ω|^3 ∂P := integral_mono hR.norm (h3.const_mul _) (fun ω => by
      simpa only [abs_mul, mul_pow] using exp_remainder_three (t*X ω))
    _ = _ := integral_const_mul _ _

lemma independent_array_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (h4 : ∀ n, MemLp (X n) 4 P)
    (h0 : ∀ n, ∫ ω, X n ω ∂P = 0) (m : ℕ → ℕ)
    (hm : ∀ᶠ n in atTop, 1 ≤ m n) (v : ℝ)
    (h2zero : Tendsto (fun n => ∫ ω, (X n ω)^2 ∂P) atTop (𝓝 0))
    (h2scaled : Tendsto (fun n => (m n:ℝ)*(∫ ω, (X n ω)^2 ∂P)) atTop (𝓝 v))
    (h4scaled : Tendsto (fun n => (m n:ℝ)*(∫ ω, (X n ω)^4 ∂P)) atTop (𝓝 0))
    (t : ℝ) : Tendsto (fun n => (charFun (P.map (X n)) t)^m n)
      atTop (𝓝 (Complex.exp (-(t:ℂ)^2*v/2))) := by
  let z : ℕ → ℂ := fun n => charFun (P.map (X n)) t
  let e : ℕ → ℂ := fun n => z n - (1 - (t:ℂ)^2*(∫ ω, (X n ω)^2 ∂P)/2)
  have h3 : Tendsto (fun n => (m n:ℝ)*(∫ ω, |X n ω|^3 ∂P)) atTop (𝓝 0) := by
    have hs := (h2scaled.sqrt).mul (h4scaled.sqrt)
    simp only [Real.sqrt_zero, mul_zero] at hs
    apply squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun ω => by positivity)) _ hs
    intro n
    calc
      _ ≤ (m n:ℝ)*(Real.sqrt (∫ ω, (X n ω)^2 ∂P)*Real.sqrt (∫ ω, (X n ω)^4 ∂P)) :=
        mul_le_mul_of_nonneg_left (third_moment_le P (X n) (h4 n)) (Nat.cast_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg (m n)), Real.sqrt_mul (Nat.cast_nonneg (m n))]
        rw [show Real.sqrt (m n) * Real.sqrt (∫ ω, (X n ω)^2 ∂P) *
          (Real.sqrt (m n) * Real.sqrt (∫ ω, (X n ω)^4 ∂P)) =
          (Real.sqrt (m n))^2 * (Real.sqrt (∫ ω, (X n ω)^2 ∂P) *
          Real.sqrt (∫ ω, (X n ω)^4 ∂P)) by ring, Real.sq_sqrt (Nat.cast_nonneg (m n))]
  have hem : Tendsto (fun n => (m n:ℂ)*e n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using h3.const_mul (|t|^3))
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (m n:ℝ)*(|t|^3*(∫ ω, |X n ω|^3 ∂P)) :=
        mul_le_mul_of_nonneg_left (charFun_cubic_error P (X n) (hX n) (h4 n) (h0 n) t) (Nat.cast_nonneg _)
      _ = _ := by ring
  have he0 : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_norm_zero.comp hem)
    filter_upwards [hm] with n hn
    simp only [Function.comp_apply, norm_mul, Complex.norm_natCast]
    exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hn)
  have hz : Tendsto z atTop (𝓝 1) := by
    have hs := ((tendsto_const_nhds (x := (1:ℂ))).sub ((Complex.continuous_ofReal.tendsto 0 |>.comp h2zero).const_mul ((t:ℂ)^2) |>.div_const 2)).add he0
    convert hs using 1 <;> simp [e] <;> ring
  apply tendsto_pow_of_scaled_sub hz
  have hv := (Complex.continuous_ofReal.tendsto v).comp h2scaled
  have ha := ((hv.const_mul (-(t:ℂ)^2)).div_const 2).add hem
  convert ha using 1
  · ext n
    dsimp [e]
    push_cast
    ring
  · simp

end IndependentArrayAux

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

private lemma identDistrib_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ (fun n => hY (n + k))),
    Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ hY)] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    ∃ p q : ℕ → ℕ,
      (∀ n, 0 < p n) ∧
      Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      Tendsto (fun n : ℕ => (p n : ℝ) / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((n - (n / (p n + q n)) * p n : ℕ) : ℝ) / n)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((n / (p n + q n) - 1 : ℕ) : ℝ) *
        alphaMixingCoef P Y (q n + 1)) atTop (𝓝 0) ∧
      ∀ t : ℝ, Tendsto (fun n : ℕ =>
        (charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (p n), Y i ω)) t) ^
          (n / (p n + q n)))
        atTop (𝓝 (charFun (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) t)) := by
  classical
  let S : ℕ → Ω → ℝ := fun r ω => ∑ i ∈ Finset.range r, Y i ω
  have hL (i : ℕ) (a : ℝ≥0∞) : MemLp (Y i) a P :=
    MemLp.of_bound (hY i).aestronglyMeasurable |B| ((hB i).mono fun ω hω => by
      simpa only [Real.norm_eq_abs] using hω.le.trans (le_abs_self B))
  have hSL (r : ℕ) (a : ℝ≥0∞) : MemLp (S r) a P := memLp_finsetSum _ (fun i _ => hL i a)
  have hSm (r : ℕ) : Measurable (S r) := by dsimp [S]; fun_prop
  have hmean (i : ℕ) : ∫ ω, Y i ω ∂P = 0 := (identDistrib_coord P Y hY hstat i).integral_eq.trans hcent
  have hS0 (r : ℕ) : ∫ ω, S r ω ∂P = 0 := by
    rw [show S r = fun ω => ∑ i ∈ Finset.range r, Y i ω by rfl,
      integral_finsetSum _ (fun i _ => (hL i 1).integrable le_rfl)]
    simp [hmean]
  have hSV (r : ℕ) : (∫ ω, (S r ω)^2 ∂P) = Var[∑ i ∈ Finset.range r, Y i; P] := by
    rw [← variance_of_integral_eq_zero (hSm r).aemeasurable (hS0 r)]
    congr 1; ext ω; simp [S]
  let γ : ℕ → ℝ := fun r => (∫ ω, (S r ω)^4 ∂P)/(r:ℝ)^3
  have hγ : Tendsto γ atTop (𝓝 0) :=
    _root_.NumberBoundedPort_MarkovChainCLT_tendsto_integral_pow_four_partialSum_div_cube_of_bounded_of_summable_alpha.solution P Y hY hstat hcent B hB hα
  have hγpos (r : ℕ) : 0 ≤ γ r := div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)
  obtain ⟨p,q,hpp,hpt,hqt,hpr,hR,hfour,hcount⟩ := AdaptiveBlockAux.exists_schedule hγ hγpos
  let m : ℕ → ℕ := fun n => n/(p n+q n)
  have hmp (n : ℕ) : m n*p n ≤ n := (Nat.mul_le_mul_left (m n) (Nat.le_add_right _ _)).trans (Nat.div_mul_le_self _ _)
  have hfrac : Tendsto (fun n => (m n:ℝ)*(p n:ℝ)/n) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1-((n-m n*p n:ℕ):ℝ)/n) atTop (𝓝 1) by simpa using tendsto_const_nhds.sub hR).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
    rw [Nat.cast_sub (hmp n), Nat.cast_mul]
    field_simp
    <;> ring
  have hmpos : ∀ᶠ n in atTop, 1 ≤ m n := by
    filter_upwards [hfrac.eventually_const_lt (by norm_num : (0:ℝ)<1)] with n hn
    by_contra hc
    have hz : m n = 0 := by omega
    simp [hz] at hn
  let X : ℕ → Ω → ℝ := fun n ω => (Real.sqrt n)⁻¹ * S (p n) ω
  have hXm (n : ℕ) : Measurable (X n) := (hSm _).const_mul _
  have hX4 (n : ℕ) : MemLp (X n) 4 P := (hSL _ 4).const_mul _
  have hX0 (n : ℕ) : ∫ ω, X n ω ∂P = 0 := by simp [X, integral_const_mul, hS0]
  have hXsq (n : ℕ) : (∫ ω, (X n ω)^2 ∂P) = Var[∑ i ∈ Finset.range (p n), Y i; P]/n := by
    simp only [X, mul_pow, integral_const_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), hSV, div_eq_mul_inv, mul_comm]
  have hXp4 (n : ℕ) : (∫ ω, (X n ω)^4 ∂P) = (∫ ω, (S (p n) ω)^4 ∂P)/(n:ℝ)^2 := by
    simp only [X, mul_pow, integral_const_mul]
    have he : ((Real.sqrt n)⁻¹)^4 = ((n:ℝ)^2)⁻¹ := by
      rw [show (4:ℕ)=2*2 by rfl, pow_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), inv_pow]
    rw [he]; ring
  have h2z : Tendsto (fun n => ∫ ω, (X n ω)^2 ∂P) atTop (𝓝 0) := by
    have ht := hpr.mul (hvarlim.comp hpt)
    simp only [zero_mul] at ht
    apply ht.congr
    intro n
    rw [hXsq]
    simp only [Function.comp_apply]
    have hp : (p n:ℝ) ≠ 0 := by exact_mod_cast (hpp n).ne'
    field_simp
  have h2v : Tendsto (fun n => (m n:ℝ)*(∫ ω, (X n ω)^2 ∂P)) atTop (𝓝 (seqAsymptoticVariance P Y)) := by
    have ht := hfrac.mul (hvarlim.comp hpt)
    simp only [one_mul] at ht
    apply ht.congr
    intro n
    rw [hXsq]
    simp only [Function.comp_apply]
    have hp : (p n:ℝ) ≠ 0 := by exact_mod_cast (hpp n).ne'
    field_simp
  have h4z : Tendsto (fun n => (m n:ℝ)*(∫ ω, (X n ω)^4 ∂P)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun ω => by positivity)) _ hfour
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hp : (0:ℝ)<p n := by exact_mod_cast hpp n
    have hmpR : (m n:ℝ)*(p n:ℝ) ≤ n := by exact_mod_cast hmp n
    rw [hXp4]
    change (m n:ℝ)*((∫ ω, (S (p n) ω)^4 ∂P)/(n:ℝ)^2) ≤ _
    have hI : 0 ≤ ∫ ω, (S (p n) ω)^4 ∂P := integral_nonneg fun ω => by positivity
    dsimp [γ]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hmpR hI]
  have ha : Tendsto (fun r : ℕ => (r:ℝ)*alphaMixingCoef P Y r) atTop (𝓝 0) := _root_.NumberBoundedPort_MarkovChainCLT_tendsto_nat_mul_alphaMixingCoef_of_summable.solution P Y hα
  have hg : Tendsto (fun n => ((m n-1:ℕ):ℝ)*alphaMixingCoef P Y (q n+1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (alphaMixingCoef_nonneg P Y _)) _ (by
      simpa using (ha.comp hqt).const_mul 4)
    filter_upwards [hcount] with n hn
    have hp : (0:ℝ) < p n := by exact_mod_cast hpp n
    have hmR : (m n:ℝ) ≤ (n:ℝ)/(p n:ℝ) := (le_div_iff₀ hp).mpr (by exact_mod_cast hmp n)
    have hm1 : ((m n-1:ℕ):ℝ) ≤ m n := by exact_mod_cast Nat.sub_le (m n) 1
    calc
      _ ≤ (4*(q n:ℝ))*alphaMixingCoef P Y (q n) := mul_le_mul (hm1.trans (hmR.trans hn))
        (_root_.NumberBoundedPort_MarkovChainCLT_alphaMixingCoef_antitone.solution P Y (Nat.le_succ _)) (alphaMixingCoef_nonneg P Y _) (by positivity)
      _ = _ := by ring
  refine ⟨p,q,hpp,hpt,hqt,hpr,hR,hg,?_⟩
  intro t
  have ht := IndependentArrayAux.independent_array_limit P X hXm hX4 hX0 m hmpos
    (seqAsymptoticVariance P Y) h2z h2v h4z t
  convert ht using 1
  rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_add, Real.coe_toNNReal _ hvar.le]
  congr 1
  push_cast
  ring

end NumberBoundedPort_MarkovChainCLT_exists_independent_blocks_of_bounded_of_summable_alpha


namespace NumberBoundedPort_MarkovChainCLT_charFun_sub_le_of_small_selection

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

private lemma identDistrib_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ (fun n => hY (n + k))),
    Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ hY)] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

private lemma exp_diff_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x-y| := by
  have he : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((x-y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

private lemma integral_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (hD : MemLp D 2 P) :
    (∫ ω, |D ω| ∂P) ≤ Real.sqrt (∫ ω, (D ω)^2 ∂P) := by
  have hv := variance_nonneg (fun ω => |D ω|) P
  simp only [← Real.norm_eq_abs] at hv
  rw [variance_eq_sub hD.norm] at hv
  simp only [Pi.pow_apply, Real.norm_eq_abs, sq_abs] at hv
  apply (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => sq_nonneg _)).2
  linarith

private lemma charFun_diff_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hD : MemLp (F-G) 2 P) (t : ℝ) :
    ‖charFun (P.map F) t - charFun (P.map G) t‖ ≤
      |t| * Real.sqrt (∫ ω, (F ω-G ω)^2 ∂P) := by
  have hfi (H : Ω → ℝ) (hH : Measurable H) :
      Integrable (fun ω => Complex.exp (((t * H ω : ℝ) : ℂ) * Complex.I)) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact ae_of_all _ fun ω => (Complex.norm_exp_ofReal_mul_I _).le
  rw [charFun_apply_real, charFun_apply_real,
    integral_map hF.aemeasurable (by fun_prop), integral_map hG.aemeasurable (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  rw [← integral_sub (hfi F hF) (hfi G hG)]
  calc
    _ ≤ ∫ ω, ‖Complex.exp (((t * F ω : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * G ω : ℝ) : ℂ) * Complex.I)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |F ω-G ω| ∂P := by
      apply integral_mono ((hfi F hF).sub (hfi G hG)).norm
        ((hD.integrable (by norm_num)).norm.const_mul |t|)
      intro ω
      simpa only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul] using exp_diff_le (t * F ω) (t * G ω)
    _ = |t| * ∫ ω, |F ω-G ω| ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt P (F-G) hD) (abs_nonneg t)

/-- Removing a finite selection gives an explicit characteristic-function error. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k+1) ω ∂P|))
    (n : ℕ) (s : Finset ℕ) (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hsub : ∀ ω, F ω - G ω = (Real.sqrt n)⁻¹ * ∑ i ∈ s, Y i ω)
    (t : ℝ) :
    ‖charFun (P.map F) t - charFun (P.map G) t‖ ≤ |t| * Real.sqrt
      (((s.card : ℝ) / n) * ((∫ ω, (Y 0 ω)^2 ∂P) +
        2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k+1) ω ∂P|)) := by
  classical
  have hmem (i : ℕ) : MemLp (Y i) 2 P := (identDistrib_coord P Y hY hstat i).symm.memLp_snd hL2
  have hmean (i : ℕ) : ∫ ω, Y i ω ∂P = 0 :=
    (identDistrib_coord P Y hY hstat i).integral_eq.trans hcent
  have hS : MemLp (fun ω => ∑ i ∈ s, Y i ω) 2 P := memLp_finsetSum _ (fun i _ => hmem i)
  have hmS : Measurable (fun ω => ∑ i ∈ s, Y i ω) := by fun_prop
  have hm0 : ∫ ω, (∑ i ∈ s, Y i ω) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    simp only [hmean, Finset.sum_const_zero]
  have hfun : F-G = fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ s, Y i ω := funext hsub
  have hD : MemLp (F-G) 2 P := hfun ▸ hS.const_mul (Real.sqrt n)⁻¹
  have hv := _root_.NumberBoundedPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov.solution P Y hY hstat hcent hL2 hsum s
  have hsq : ∫ ω, (F ω-G ω)^2 ∂P =
      (n : ℝ)⁻¹ * Var[∑ i ∈ s, Y i; P] := by
    simp_rw [hsub, mul_pow]
    rw [integral_const_mul, ← variance_of_integral_eq_zero hmS.aemeasurable hm0]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [← Finset.sum_apply]
  apply (charFun_diff_le P F G hF hG hD t).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
  apply Real.sqrt_le_sqrt
  rw [hsq]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((s.card : ℝ) * _) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = _ := by ring

end NumberBoundedPort_MarkovChainCLT_charFun_sub_le_of_small_selection


namespace NumberBoundedPort_MarkovChainCLT_abs_integral_prod_sub_prod_integral_le_of_alpha

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

private theorem processSigma_mono (Y : ℕ → Ω → E) {s t : Set ℕ} (h : s ⊆ t) :
    processSigma Y s ≤ processSigma Y t := by
  refine iSup₂_le fun i hi => ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ t) => MeasurableSpace.comap (Y i) inferInstance) i (h hi)

private theorem alphaMixingCoef_nonneg' (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  refine le_csSup ⟨1, ?_⟩
    ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
      @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
  rintro r ⟨k, A, B, -, -, rfl⟩
  have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
      (measure_mono (Set.subset_univ (A ∩ B)))
  have hA1 : (P A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ A))
  have hB1 : (P B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ B))
  have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
  have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

theorem solution (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) (a b : ℕ → ℕ) (f : ℕ → Ω → ℂ) (M : ℕ → ℝ) (m : ℕ)
    (hab : ∀ j, j < m → a j ≤ b j)
    (hgap : ∀ j, j + 1 < m → b j + n ≤ a (j + 1))
    (hf : ∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j))
    (hM : ∀ j, j < m → 0 ≤ M j)
    (hfb : ∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j) :
    ‖(∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P‖
      ≤ 16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * ∏ j ∈ Finset.range m, M j := by
  have halpha : 0 ≤ alphaMixingCoef P Y n := alphaMixingCoef_nonneg' P Y n
  suffices H : ∀ m : ℕ, (∀ j, j < m → a j ≤ b j) → (∀ j, j + 1 < m → b j + n ≤ a (j + 1)) →
      (∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j)) →
      (∀ j, j < m → 0 ≤ M j) → (∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j) →
      ‖(∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P‖
        ≤ 16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * ∏ j ∈ Finset.range m, M j from
    H m hab hgap hf hM hfb
  clear hab hgap hf hM hfb m
  intro m
  induction m with
  | zero => intro _ _ _ _ _; simp
  | succ m ih =>
    intro hab hgap hf hM hfb
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp
    obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    -- restricted hypotheses, for the induction hypothesis
    have hab' : ∀ j, j < m → a j ≤ b j := fun j hj => hab j (Nat.lt_succ_of_lt hj)
    have hgap' : ∀ j, j + 1 < m → b j + n ≤ a (j + 1) := fun j hj =>
      hgap j (Nat.lt_succ_of_lt hj)
    have hf' : ∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j) :=
      fun j hj => hf j (Nat.lt_succ_of_lt hj)
    have hM' : ∀ j, j < m → 0 ≤ M j := fun j hj => hM j (Nat.lt_succ_of_lt hj)
    have hfb' : ∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j := fun j hj => hfb j (Nat.lt_succ_of_lt hj)
    have hIH := ih hab' hgap' hf' hM' hfb'
    set G : Ω → ℂ := fun ω => ∏ j ∈ Finset.range m, f j ω with hG
    set K : ℝ := ∏ j ∈ Finset.range m, M j with hK
    have hKnonneg : 0 ≤ K := Finset.prod_nonneg fun j hj => hM' j (Finset.mem_range.mp hj)
    have hMm : 0 ≤ M m := hM m (Nat.lt_succ_self m)
    -- `b` is nondecreasing along the block schedule
    have hstep : ∀ j, j < m → b j ≤ b (j + 1) := by
      intro j hj
      have h1 : b j + n ≤ a (j + 1) := hgap j (by omega)
      have h2 : a (j + 1) ≤ b (j + 1) := hab (j + 1) (by omega)
      omega
    have hmono : ∀ i j : ℕ, i ≤ j → j ≤ m → b i ≤ b j := by
      intro i j hij hjm
      induction j with
      | zero => simp_all
      | succ j ihj =>
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · have h1 : b i ≤ b j := ihj (by omega) (by omega)
          exact h1.trans (hstep j (by omega))
        · have : i = j + 1 := by omega
          subst this
          exact le_rfl
    -- measurability of the partial product with respect to the past
    have hGmeas : Measurable[processSigma Y (Set.Iic (b p))] G := by
      refine Finset.measurable_prod _ fun j hj => ?_
      have hjm : j < m := Finset.mem_range.mp hj
      refine (hf' j hjm).mono (processSigma_mono Y ?_) le_rfl
      intro x hx
      have hxb : x ≤ b j := hx.2
      have : b j ≤ b p := hmono j p (by omega) (by omega)
      exact le_trans hxb this
    -- measurability of the last factor with respect to the future
    have hfmmeas : Measurable[processSigma Y (Set.Ici (b p + n))] (f m) := by
      refine (hf m (Nat.lt_succ_self m)).mono (processSigma_mono Y ?_) le_rfl
      intro x hx
      have h1 : b p + n ≤ a (p + 1) := hgap p (by omega)
      have h2 : a m ≤ x := hx.1
      have : b p + n ≤ a m := by rw [hp]; exact h1
      exact le_trans this h2
    -- bounds
    have hGb : ∀ ω, ‖G ω‖ ≤ K := by
      intro ω
      have hnp : ‖G ω‖ = ∏ j ∈ Finset.range m, ‖f j ω‖ := by
        rw [hG]; exact Complex.norm_prod _ _
      rw [hnp]
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j hj => hfb' j (Finset.mem_range.mp hj) ω)
    have hfmb : ∀ ω, ‖f m ω‖ ≤ M m := hfb m (Nat.lt_succ_self m)
    have hintfm : ‖∫ ω, f m ω ∂P‖ ≤ M m := by
      have := norm_integral_le_of_norm_le_const (μ := P) (C := M m)
        (Filter.Eventually.of_forall hfmb)
      simpa using this
    -- the pairwise estimate at the last junction
    have hpair := _root_.NumberBoundedPort_MarkovChainCLT_alpha_cov_bounded_complex.solution P Y hY n (b p) G (f m) hGmeas
      hfmmeas K (M m) hKnonneg hMm hGb hfmb
    -- split the error into the junction error and the inductive error
    have hsplit : (∫ ω, ∏ j ∈ Finset.range (m + 1), f j ω ∂P)
          - ∏ j ∈ Finset.range (m + 1), ∫ ω, f j ω ∂P
        = ((∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P))
          + ((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P) := by
      simp only [Finset.prod_range_succ, hG]
      ring
    have hbound2 : ‖((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P)
        * (∫ ω, f m ω ∂P)‖ ≤ (16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * K) * M m := by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul hIH hintfm (norm_nonneg _)
        (by positivity)
    have hcast : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
    have hcast2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := hmpos
      push_cast [Nat.cast_sub this]
      ring
    rw [hsplit, Finset.prod_range_succ, hcast]
    calc ‖((∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P))
            + ((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P)‖
        ≤ ‖(∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P)‖
          + ‖((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P)‖ :=
          norm_add_le _ _
      _ ≤ 16 * K * M m * alphaMixingCoef P Y n
          + (16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * K) * M m :=
          add_le_add hpair hbound2
      _ = 16 * (m : ℝ) * alphaMixingCoef P Y n * (K * M m) := by
          rw [hcast2]; ring

end NumberBoundedPort_MarkovChainCLT_abs_integral_prod_sub_prod_integral_le_of_alpha


namespace NumberBoundedPort_MarkovChainCLT_charFun_sub_pow_block_le

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

private theorem block_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k+1) ω ∂P|))
    (n m g : ℕ) (a b : ℕ → ℕ) (U : ℕ → Ω → ℝ) (s : Finset ℕ)
    (hab : ∀ j, j < m → a j ≤ b j)
    (hgap : ∀ j, j+1 < m → b j + g ≤ a (j+1))
    (hU : ∀ j, Measurable[processSigma Y (Set.Icc (a j) (b j))] (U j))
    (hdecomp : ∀ ω, (∑ i ∈ Finset.range n, Y i ω) =
      (∑ j ∈ Finset.range m, U j ω) + ∑ i ∈ s, Y i ω)
    (t : ℝ) :
    ‖charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)) t -
      ∏ j ∈ Finset.range m, charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * U j ω)) t‖ ≤
    |t| * Real.sqrt (((s.card : ℝ) / n) * ((∫ ω, (Y 0 ω)^2 ∂P) +
      2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k+1) ω ∂P|)) +
      16 * ((m-1 : ℕ) : ℝ) * alphaMixingCoef P Y g := by
  classical
  have hsig (A : Set ℕ) : processSigma Y A ≤ ‹MeasurableSpace Ω› := by
    apply iSup_le; intro i; apply iSup_le; intro hi
    exact (hY i).comap_le
  have hUm (j : ℕ) : Measurable (U j) := (hU j).mono (hsig _) le_rfl
  let F : Ω → ℝ := fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω
  let G : Ω → ℝ := fun ω => (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range m, U j ω
  let f : ℕ → Ω → ℂ := fun j ω => Complex.exp (((t * ((Real.sqrt n)⁻¹ * U j ω) : ℝ) : ℂ) * Complex.I)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hsmall := _root_.NumberBoundedPort_MarkovChainCLT_charFun_sub_le_of_small_selection.solution P Y hY hstat hcent hL2 hsum n s F G hF hG
    (by intro ω; dsimp [F,G]; rw [hdecomp]; ring) t
  have hfactor := _root_.NumberBoundedPort_MarkovChainCLT_abs_integral_prod_sub_prod_integral_le_of_alpha.solution P Y hY g a b f
    (fun _ => 1) m hab hgap (by intro j hj; dsimp [f]; fun_prop)
    (by intros; norm_num) (by intro j hj ω; dsimp [f]; exact (Complex.norm_exp_ofReal_mul_I _).le)
  simp only [Finset.prod_const_one, mul_one] at hfactor
  have hprod (ω : Ω) : (∏ j ∈ Finset.range m, f j ω) =
      Complex.exp (((t * G ω : ℝ) : ℂ) * Complex.I) := by
    simp only [f, ← Complex.exp_sum]
    congr 1
    simp only [G, ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.sum_mul,
      ← Complex.ofReal_mul]
  have hmap (H : Ω → ℝ) (hH : Measurable H) : charFun (P.map H) t =
      ∫ ω, Complex.exp (((t * H ω : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hH.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have hchar : charFun (P.map G) t = ∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P := by
    rw [hmap G hG]; simp_rw [hprod]
  have hjchar (j : ℕ) : charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * U j ω)) t =
      ∫ ω, f j ω ∂P := hmap _ (by fun_prop)
  calc
    _ ≤ ‖charFun (P.map F) t - charFun (P.map G) t‖ +
      ‖charFun (P.map G) t - ∏ j ∈ Finset.range m,
        charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * U j ω)) t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hsmall (by simpa only [hchar, hjchar] using hfactor)

/-- The Bernstein big-block/small-block error for equal blocks. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k+1) ω ∂P|))
    (n p q : ℕ) (hp : 0 < p) (t : ℝ) :
    ‖charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)) t -
      (charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range p, Y i ω)) t) ^
        (n / (p+q))‖ ≤
    |t| * Real.sqrt (((n - (n/(p+q))*p : ℕ) : ℝ) / n *
      ((∫ ω, (Y 0 ω)^2 ∂P) + 2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k+1) ω ∂P|)) +
      16 * ((n/(p+q)-1 : ℕ) : ℝ) * alphaMixingCoef P Y (q+1) := by
  classical
  let m := n / (p+q)
  let a : ℕ → ℕ := fun j => j*(p+q)
  let b : ℕ → ℕ := fun j => a j+p-1
  let B : ℕ → Finset ℕ := fun j => Finset.Ico (a j) (a j+p)
  let U : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ B j, Y i ω
  let T : Finset ℕ := (Finset.range m).biUnion B
  let R := Finset.range n \ T
  have hdisj : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint B := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro k hk hkj
    have hi' := Finset.mem_Ico.mp hk
    have hj' := Finset.mem_Ico.mp hkj
    dsimp [a] at hi' hj'
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hh := Nat.mul_le_mul_right (p+q) (show i+1 ≤ j by omega)
      nlinarith
    · have hh := Nat.mul_le_mul_right (p+q) (show j+1 ≤ i by omega)
      nlinarith
  have hTsub : T ⊆ Finset.range n := by
    intro k hk
    obtain ⟨j,hj,hk⟩ := Finset.mem_biUnion.mp hk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_Ico.mp hk
    have hh := Nat.mul_le_mul_right (p+q) (show j+1 ≤ m by omega)
    have hm : m*(p+q) ≤ n := Nat.div_mul_le_self n (p+q)
    dsimp [a] at hk'
    rw [Finset.mem_range]
    nlinarith
  have hcardT : T.card = m*p := by
    rw [Finset.card_biUnion hdisj]
    simp [B]
  have hcardR : R.card = n-m*p := by
    rw [Finset.card_sdiff_of_subset hTsub, Finset.card_range, hcardT]
  have hdecomp (ω : Ω) : (∑ i ∈ Finset.range n, Y i ω) =
      (∑ j ∈ Finset.range m, U j ω) + ∑ i ∈ R, Y i ω := by
    rw [← Finset.sum_biUnion hdisj]
    exact (Finset.sum_sdiff hTsub).symm.trans (add_comm _ _)
  have hU (j : ℕ) : Measurable[processSigma Y (Set.Icc (a j) (b j))] (U j) := by
    apply Finset.measurable_sum
    intro i hi
    rw [measurable_iff_comap_le]
    apply le_iSup_of_le i
    have hi' := Finset.mem_Ico.mp hi
    have his : i ∈ Set.Icc (a j) (b j) := by dsimp [b]; constructor <;> omega
    exact le_iSup_of_le his le_rfl
  have hcomp := block_comparison P Y hY hstat hcent hL2 hsum n m (q+1) a b U R
    (by intros; dsimp [b]; omega)
    (by intro j hj; dsimp [a,b]; simp only [Nat.add_mul, Nat.one_mul]; omega)
    hU hdecomp t
  have hmapU (j : ℕ) : P.map (fun ω => (Real.sqrt n)⁻¹ * U j ω) =
      P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range p, Y i ω) := by
    let H : (ℕ → ℝ) → ℝ := fun z => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range p, z i
    have hH : Measurable H := by dsimp [H]; fun_prop
    have hh := congrArg (Measure.map H) (hstat (a j))
    rw [Measure.map_map hH (measurable_pi_lambda _ (fun i => hY (i+a j))),
      Measure.map_map hH (measurable_pi_lambda _ hY)] at hh
    convert hh using 1 <;> first | rfl | (congr 1; funext ω; simp [Function.comp_def, U, B, H, Finset.sum_Ico_eq_sum_range, Nat.add_comm])
  simp_rw [hmapU] at hcomp
  simpa only [hcardR, Finset.prod_const, Finset.card_range, m] using hcomp

end NumberBoundedPort_MarkovChainCLT_charFun_sub_pow_block_le

section OwnCandidate
open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)  := by
  obtain ⟨p,q,hp,_hpTop,_hqTop,_hpn,hrem,hmix,hind⟩ :=
    _root_.NumberBoundedPort_MarkovChainCLT_exists_independent_blocks_of_bounded_of_summable_alpha.solution P Y hY hstat hcent B hB hα hvarlim hvar
  have hL2 : MemLp (Y 0) 2 P := MemLp.of_bound (hY 0).aestronglyMeasurable B
    ((hB 0).mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω.le)
  have hsum := _root_.NumberBoundedPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha.solution P Y hY hstat hcent B hB hα
  have habs : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k+1) ω ∂P|) := by
    simpa only [Real.norm_eq_abs] using hsum.norm
  let C : ℝ := (∫ ω, (Y 0 ω)^2 ∂P) + 2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k+1) ω ∂P|
  have hcf : ∀ t : ℝ, Tendsto (fun n : ℕ =>
      charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)) t)
      atTop (𝓝 (charFun (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) t)) := by
    intro t
    have herr : Tendsto (fun n : ℕ =>
        |t| * Real.sqrt ((((n - (n / (p n + q n)) * p n : ℕ) : ℝ) / n) * C) +
        16 * (((n / (p n + q n) - 1 : ℕ) : ℝ) * alphaMixingCoef P Y (q n+1)))
        atTop (𝓝 0) := by
      simpa using ((hrem.mul_const C).sqrt.const_mul |t|).add (hmix.const_mul 16)
    have hdiff : Tendsto (fun n : ℕ =>
        charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)) t -
        (charFun (P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (p n), Y i ω)) t) ^
          (n / (p n+q n))) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ herr
      intro n
      simpa only [C, mul_assoc] using
        _root_.NumberBoundedPort_MarkovChainCLT_charFun_sub_pow_block_le.solution P Y hY hstat hcent hL2 habs n (p n) (q n) (hp n) t
    simpa using hdiff.add (hind t)
  refine ⟨fun n => (show Measurable (fun ω => (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, Y i ω) from by fun_prop).aemeasurable, measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simpa only [Measure.map_id, ProbabilityMeasure.coe_mk] using hcf t

end OwnCandidate
#print axioms solution