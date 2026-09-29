-- Prove2me | solution 1 for MarkovChainCLT.clt_of_moment_of_alpha_pow_summable
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:21:06.903476+00:00
-- url     : https://prove2.me/submissions/58bdb0f0-1af9-4923-9a4a-3b1d7d06a685

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_bounded
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NumberMomentPort_LayerCake_bounded_layercake_identity

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

end NumberMomentPort_LayerCake_bounded_layercake_identity


namespace NumberMomentPort_LayerCake_expectation_add_const

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
    fun ω => _root_.NumberMomentPort_LayerCake_bounded_layercake_identity.solution (W ω) M (hWb ω)
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

end NumberMomentPort_LayerCake_expectation_add_const


namespace NumberMomentPort_ProbabilityTheory_cov_indicator_eq

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

end NumberMomentPort_ProbabilityTheory_cov_indicator_eq


namespace NumberMomentPort_MarkovChainCLT_processSigma_le_of_measurable

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

end NumberMomentPort_MarkovChainCLT_processSigma_le_of_measurable


namespace NumberMomentPort_MarkovChainCLT_alpha_indicator_cov_le

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

end NumberMomentPort_MarkovChainCLT_alpha_indicator_cov_le


namespace NumberMomentPort_MarkovChainCLT_alpha_cov_bounded

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
    _root_.NumberMomentPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberMomentPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
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
    fun t s => _root_.NumberMomentPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y n k _ _ (hAt t) (hBs s)
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
    fun ω => _root_.NumberMomentPort_LayerCake_bounded_layercake_identity.solution (U ω) M (hUb ω)
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
    _root_.NumberMomentPort_LayerCake_expectation_add_const.solution P V hVm M (fun ω => hVb ω)
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
      _root_.NumberMomentPort_LayerCake_bounded_layercake_identity.solution (V ω) M (hVb ω)
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
      _root_.NumberMomentPort_ProbabilityTheory_cov_indicator_eq.solution P _ _ (hAt_amb q.1) (hBs_amb q.2)
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


end NumberMomentPort_MarkovChainCLT_alpha_cov_bounded


namespace NumberMomentPort_MarkovChainCLT_stationary_mean_transfer

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

end NumberMomentPort_MarkovChainCLT_stationary_mean_transfer


namespace NumberMomentPort_MarkovChainCLT_stationary_memLp_transfer

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

end NumberMomentPort_MarkovChainCLT_stationary_memLp_transfer


namespace NumberMomentPort_MarkovChainCLT_alpha_cov_bound_of_moment

open MeasureTheory

namespace CovarianceTail

noncomputable def trunc (T x : ℝ) : ℝ := if |x| ≤ T then x else 0

theorem measurable_trunc (T : ℝ) : Measurable (trunc T) := by
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
    measurable_id measurable_const

theorem trunc_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |trunc T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simpa [trunc, hx] using hx
  · simpa [trunc, hx] using hT

theorem trunc_abs_le (T x : ℝ) : |trunc T x| ≤ |x| := by
  by_cases hx : |x| ≤ T
  · simp [trunc, hx]
  · simpa [trunc, hx] using abs_nonneg x

theorem sq_le_rpow_div (δ T a : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (ha : T ≤ a) : a ^ 2 ≤ a ^ (2 + δ) / T ^ δ := by
  have ha0 : 0 < a := hT.trans_le ha
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT δ)).mpr
  calc
    a ^ 2 * T ^ δ ≤ a ^ 2 * a ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT.le ha hδ.le) (sq_nonneg a)
    _ = a ^ (2 + δ) := by rw [Real.rpow_add ha0, Real.rpow_two]

theorem abs_mul_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hout : T < |x| ∨ T < |y|) :
    |x * y| ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  have hden : 0 ≤ T ^ δ := (Real.rpow_pos_of_pos hT δ).le
  by_cases hxy : |x| ≤ |y|
  · have hyT : T ≤ |y| := by
      rcases hout with hx | hy
      · exact (hx.trans_le hxy).le
      · exact hy.le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hyT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ)]
  · have hyx : |y| ≤ |x| := (lt_of_not_ge hxy).le
    have hxT : T ≤ |x| := by
      rcases hout with hx | hy
      · exact hx.le
      · exact (hy.trans_le hyx).le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
      _ ≤ |x| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |x| hδ hT hxT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg y) (2 + δ)]

theorem product_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    |x * y - trunc T x * trunc T y| ≤
      (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  by_cases hx : |x| ≤ T
  · by_cases hy : |y| ≤ T
    · simp only [trunc, hx, hy, if_true, sub_self, abs_zero]
      positivity
    · simpa [trunc, hx, hy] using
        abs_mul_tail_bound δ T x y hδ hT (Or.inr (lt_of_not_ge hy))
  · simpa [trunc, hx] using
      abs_mul_tail_bound δ T x y hδ hT (Or.inl (lt_of_not_ge hx))

theorem single_tail_bound (δ T y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    T * |y - trunc T y| ≤ |y| ^ (2 + δ) / T ^ δ := by
  by_cases hy : |y| ≤ T
  · simp only [trunc, hy, if_true, sub_self, abs_zero, mul_zero]
    positivity
  · have hTy : T ≤ |y| := (lt_of_not_ge hy).le
    simp only [trunc, hy, if_false, sub_zero]
    calc
      T * |y| ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hTy

theorem abs_mul_le_one_add_rpow (δ x y : ℝ) (hδ : 0 < δ) :
    |x * y| ≤ 1 + |x| ^ (2 + δ) + |y| ^ (2 + δ) := by
  by_cases hx : |x| ≤ 1
  · by_cases hy : |y| ≤ 1
    · have hprod : |x * y| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg x, abs_nonneg y,
          mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
      linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ),
        Real.rpow_nonneg (abs_nonneg y) (2 + δ)]
    · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
        (Or.inr (lt_of_not_ge hy))
      simp only [Real.one_rpow, div_one] at h
      linarith
  · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
      (Or.inl (lt_of_not_ge hx))
    simp only [Real.one_rpow, div_one] at h
    linarith

end CovarianceTail

open MeasureTheory ProbabilityTheory MarkovChainCLT

namespace CovarianceStationarity

theorem identDistrib_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hshift : Measurable (fun ω n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hfull : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) hshift,
    Measure.map_map (measurable_pi_apply 0) hfull] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

theorem measurable_coord {Ω : Type*} (Y : ℕ → Ω → ℝ) (s : Set ℕ)
    (i : ℕ) (hi : i ∈ s) : Measurable[processSigma Y s] (Y i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem alpha_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _

end CovarianceStationarity

open MeasureTheory ProbabilityTheory CovarianceTail
open scoped ProbabilityTheory

namespace CovarianceIntegral

theorem truncation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (δ T M a : ℝ)
    (hδ : 0 < δ) (hT : 0 < T)
    (hXm : Integrable (fun ω => |X ω| ^ (2 + δ)) P)
    (hZm : Integrable (fun ω => |Z ω| ^ (2 + δ)) P)
    (hXM : ∫ ω, |X ω| ^ (2 + δ) ∂P = M)
    (hZM : ∫ ω, |Z ω| ^ (2 + δ) ∂P = M)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hc : |cov[fun ω => trunc T (X ω), fun ω => trunc T (Z ω); P]| ≤ 4 * T ^ 2 * a) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := by
  let U := fun ω => trunc T (X ω)
  let V := fun ω => trunc T (Z ω)
  have hUm : MemLp U 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hX).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (X ω))
  have hVm : MemLp V 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hZ).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (Z ω))
  have hUi : Integrable U P := hUm.integrable (by norm_num)
  have hVi : Integrable V P := hVm.integrable (by norm_num)
  have hUV : Integrable (fun ω => U ω * V ω) P := hUm.integrable_mul hVm
  have hXZ : Integrable (fun ω => X ω * Z ω) P := by
    refine (((integrable_const (1 : ℝ)).add hXm).add hZm).mono'
      (hX.mul hZ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_mul_le_one_add_rpow δ (X ω) (Z ω) hδ
  have hZi : Integrable Z P := by
    have hzNorm : Integrable (fun ω => ‖Z ω‖ ^ (1 : ℝ)) P :=
      integrable_norm_rpow_of_le (p := 1) (q := 2 + δ) hZ.aestronglyMeasurable (by norm_num)
        (by linarith) (by linarith)
        (by simpa only [Real.norm_eq_abs] using hZm)
    have hn : Integrable (fun ω => ‖Z ω‖) P := by simpa only [Real.rpow_one] using hzNorm
    exact hn.mono' hZ.aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤
      (M + M) / T ^ δ := by
    rw [← integral_sub hXZ hUV]
    calc
      |∫ ω, X ω * Z ω - U ω * V ω ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|X ω| ^ (2 + δ) + |Z ω| ^ (2 + δ)) / T ^ δ ∂P :=
        integral_mono_ae (hXZ.sub hUV).abs ((hXm.add hZm).div_const (T ^ δ))
          (ae_of_all _ fun ω => product_tail_bound δ T (X ω) (Z ω) hδ hT)
      _ = (M + M) / T ^ δ := by rw [integral_div, integral_add hXm hZm, hXM, hZM]
  have hsingle : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [← integral_sub hZi hVi]
    calc
      T * |∫ ω, Z ω - V ω ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
      _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
      _ ≤ ∫ ω, |Z ω| ^ (2 + δ) / T ^ δ ∂P :=
        integral_mono_ae ((hZi.sub hVi).abs.const_mul T) (hZm.div_const (T ^ δ))
          (ae_of_all _ fun ω => single_tail_bound δ T (Z ω) hδ hT)
      _ = M / T ^ δ := by rw [integral_div, hZM]
  have hEV : T * |∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    simpa only [hZ0, zero_sub, abs_neg] using hsingle
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc
      |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P := integral_mono_ae hUi.abs (integrable_const T)
        (ae_of_all _ fun ω => trunc_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * a + M / T ^ δ := by
    calc
      |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
        congr 1
        simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * a + M / T ^ δ := add_le_add hc hbias
  calc
    |∫ ω, X ω * Z ω ∂P| =
        |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
      rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| :=
      abs_add_le _ _
    _ ≤ (M + M) / T ^ δ + (4 * T ^ 2 * a + M / T ^ δ) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * a + 3 * M / T ^ δ := by ring

end CovarianceIntegral

open Filter Topology

namespace CovarianceOptimize

theorem optimize (δ M a v : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (h : ∀ T : ℝ, 0 < T → v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ) :
    v ≤ (4 + 3 * M) * a ^ (δ / (2 + δ)) := by
  have hp : 0 < 2 + δ := by linarith
  have hr : 0 < δ / (2 + δ) := div_pos hδ hp
  by_cases ha0 : a = 0
  · subst a
    have hlim : Tendsto (fun T : ℝ => 3 * M / T ^ δ) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hδ).const_div_atTop (3 * M)
    have hv : v ≤ 0 := by
      apply ge_of_tendsto hlim
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simpa only [mul_zero, zero_add] using h T hT
    simpa only [Real.zero_rpow hr.ne', mul_zero] using hv
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let q : ℝ := -1 / (2 + δ)
    let r : ℝ := δ / (2 + δ)
    let T : ℝ := a ^ q
    have hT : 0 < T := Real.rpow_pos_of_pos ha' q
    have hfirst : T ^ 2 * a = a ^ r := by
      calc
        T ^ 2 * a = a ^ (q * 2) * a ^ (1 : ℝ) := by
          rw [Real.rpow_mul ha, Real.rpow_two, Real.rpow_one]
        _ = a ^ (q * 2 + 1) := (Real.rpow_add ha' _ _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          field_simp
          ring
    have hsecond : (T ^ δ)⁻¹ = a ^ r := by
      calc
        (T ^ δ)⁻¹ = (a ^ (q * δ))⁻¹ := by rw [Real.rpow_mul ha]
        _ = a ^ (-(q * δ)) := (Real.rpow_neg ha _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          ring
    calc
      v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := h T hT
      _ = (4 + 3 * M) * a ^ r := by
        rw [div_eq_mul_inv, hsecond]
        nlinarith [hfirst]
      _ = (4 + 3 * M) * a ^ (δ / (2 + δ)) := rfl

end CovarianceOptimize

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (δ : ℝ) (hδ : 0 < δ)
    (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| ≤ C * alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ)) := by
  let M := ∫ ω, |Y 0 ω| ^ (2 + δ) ∂P
  have hM : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨4 + 3 * M, by positivity, ?_⟩
  intro k
  apply CovarianceOptimize.optimize δ M (alphaMixingCoef P Y (k + 1))
    (|∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) hδ hM
    (CovarianceStationarity.alpha_nonneg P Y (k + 1))
  intro T hT
  have hid := CovarianceStationarity.identDistrib_coord P Y hY hstat (k + 1)
  have hpow : Measurable (fun x : ℝ => |x| ^ (2 + δ)) := by fun_prop
  have hkm : Integrable (fun ω => |Y (k + 1) ω| ^ (2 + δ)) P :=
    (hid.comp hpow).integrable_iff.mpr hmom
  have hkM : ∫ ω, |Y (k + 1) ω| ^ (2 + δ) ∂P = M := (hid.comp hpow).integral_eq
  have hk0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  apply CovarianceIntegral.truncation_estimate P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    δ T M (alphaMixingCoef P Y (k + 1)) hδ hT hmom hkm rfl hkM hk0
  exact _root_.NumberMomentPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0
    (fun ω => CovarianceTail.trunc T (Y 0 ω))
    (fun ω => CovarianceTail.trunc T (Y (k + 1) ω))
    ((CovarianceTail.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Iic 0) 0 (by simp)))
    ((CovarianceTail.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
    T hT.le (fun ω => CovarianceTail.trunc_bound hT.le (Y 0 ω))
    (fun ω => CovarianceTail.trunc_bound hT.le (Y (k + 1) ω))



end NumberMomentPort_MarkovChainCLT_alpha_cov_bound_of_moment


namespace NumberMomentPort_MarkovChainCLT_summable_covariance_of_alpha_pow_summable

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  obtain ⟨C, _, hbound⟩ :=
    _root_.NumberMomentPort_MarkovChainCLT_alpha_cov_bound_of_moment.solution P Y hY hstat hcent δ hδ hmom
  have hsum : Summable (fun k : ℕ => C * alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ))) :=
    ((summable_nat_add_iff 1).2 hα).mul_left C
  exact Summable.of_norm_bounded hsum fun k => by simpa using hbound k

end NumberMomentPort_MarkovChainCLT_summable_covariance_of_alpha_pow_summable


namespace NumberMomentPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov

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

end NumberMomentPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov


namespace NumberMomentPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P Y)) := by
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
  have hprod : ∀ i j : ℕ, Integrable (fun ω => Y i ω * Y j ω) P :=
    fun i j => (hmemLp i).integrable_mul (hmemLp j)
  have hexp : ∀ n : ℕ, (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ ω, Y i ω * Y j ω ∂P := by
    intro n
    have hsq : (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2)
        = (fun ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Y i ω * Y j ω) := by
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [hsq, integral_finsetSum (Finset.range n)
      (fun i _ => integrable_finsetSum (Finset.range n) (fun j _ => hprod i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finsetSum (Finset.range n) (fun j _ => hprod i j)
  have hF : ∀ n : ℕ, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ ω, Y i ω * Y j ω ∂P)
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcol : ∑ i ∈ Finset.range n, (∫ ω, Y i ω * Y n ω ∂P)
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e1 : ∀ i ∈ Finset.range n, (∫ ω, Y i ω * Y n ω ∂P) = c ((n - 1 - i) + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hiN : i ≤ n := Nat.le_of_lt hi
          have h1 : i + (n - i) = n := Nat.add_sub_cancel' hiN
          have h := hpair i (n - i)
          have hni : n - i = (n - 1 - i) + 1 := by omega
          rw [h1] at h
          rw [hni] at h
          exact h
        rw [Finset.sum_congr rfl e1]
        exact Finset.sum_range_reflect (fun j => c (j + 1)) n
      have hrow : ∑ j ∈ Finset.range n, (∫ ω, Y n ω * Y j ω ∂P)
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e : ∀ j ∈ Finset.range n, (∫ ω, Y n ω * Y j ω ∂P)
            = (∫ ω, Y j ω * Y n ω ∂P) :=
          fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
        rw [Finset.sum_congr rfl e]
        exact hcol
      have hdiag : (∫ ω, Y n ω * Y n ω ∂P) = c 0 := by
        have h := hpair n 0
        simpa using h
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih, hcol, hrow, hdiag]
      push_cast
      ring
  have hE : ∀ n : ℕ, (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) :=
    fun n => (hexp n).trans (hF n)
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
    = (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
  rw [hE n]
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end NumberMomentPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum


namespace NumberMomentPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

-- Scratch: direct proof of `_root_.NumberMomentPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov.solution`.
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

end NumberMomentPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov


namespace NumberMomentPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha

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
      exact _root_.NumberMomentPort_MarkovChainCLT_stationary_mean_transfer.solution P Y hY hstat hcent (k + 1)
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
          exact _root_.NumberMomentPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0 U' V'
            hU'past hV'fut _ (abs_nonneg _) hU'b hV'b
  -- Comparison with the summable α series.
  have hsum : Summable (fun k : ℕ => 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1)) :=
    ((summable_nat_add_iff 1).2 hα).mul_left _
  exact Summable.of_norm_bounded hsum fun k => by simpa using hkey k

end NumberMomentPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha


namespace NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha

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
    _root_.NumberMomentPort_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov.solution P Y hY hstat hcent hL2 hsum
  exact clt_of_var_limit_of_bounded P Y hY hstat hcent B hB hα hlim hvar

end NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha


namespace NumberMomentPort_MarkovChainCLT_alphaMixingCoef_le_quarter

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-!
`α(n) ≤ 1/4`.  Each element of the defining set is `|c - a b|` with `a = P A`, `b = P B`,
`c = P (A ∩ B)`, and these satisfy `max (0, a + b - 1) ≤ c ≤ min (a, b)`; the elementary
consequence is `|c - a b| ≤ 1/4`.
-/

theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n ≤ 1 / 4 := by
  have hle : ∀ s : Set ℕ, processSigma Y s ≤ ‹MeasurableSpace Ω› :=
    fun s => iSup₂_le fun i _ => (hY i).comap_le
  have key : ∀ A B : Set Ω, MeasurableSet B →
      |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ 1 / 4 := by
    intro A B hB
    set a := (P A).toReal with ha
    set b := (P B).toReal with hb
    set c := (P (A ∩ B)).toReal with hc
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    have ha1 : a ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ A))
    have hb1 : b ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ B))
    have hca : c ≤ a :=
      ENNReal.toReal_mono (measure_ne_top P A) (measure_mono Set.inter_subset_left)
    have hcb : c ≤ b :=
      ENNReal.toReal_mono (measure_ne_top P B) (measure_mono Set.inter_subset_right)
    have hunion : P A + P B = P (A ∪ B) + P (A ∩ B) := (measure_union_add_inter A hB).symm
    have hlow : a + b - 1 ≤ c := by
      have h1 : (P (A ∪ B)).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
          (measure_mono (Set.subset_univ (A ∪ B)))
      have h2 : a + b = (P (A ∪ B)).toReal + c := by
        rw [ha, hb, hc, ← ENNReal.toReal_add (measure_ne_top P A) (measure_ne_top P B),
          ← ENNReal.toReal_add (measure_ne_top P (A ∪ B)) (measure_ne_top P (A ∩ B)), hunion]
      linarith
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
    · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  refine csSup_le ⟨0, ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
    @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩⟩ ?_
  rintro r ⟨k, A, B, -, hB, rfl⟩
  exact key A B (hle _ B hB)

end NumberMomentPort_MarkovChainCLT_alphaMixingCoef_le_quarter


namespace NumberMomentPort_MarkovChainCLT_charFun_tendsto_of_alpha_pow_summable
/- The quantitative covariance estimate below is adapted from ryanshin's
accepted proof c21f0eae-d4d4-4824-a4ef-8cdf05013f18. -/

open MeasureTheory

namespace MomentCovTail

noncomputable def trunc (T x : ℝ) : ℝ := if |x| ≤ T then x else 0

theorem measurable_trunc (T : ℝ) : Measurable (trunc T) := by
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
    measurable_id measurable_const

theorem trunc_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |trunc T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simpa [trunc, hx] using hx
  · simpa [trunc, hx] using hT

theorem trunc_abs_le (T x : ℝ) : |trunc T x| ≤ |x| := by
  by_cases hx : |x| ≤ T
  · simp [trunc, hx]
  · simpa [trunc, hx] using abs_nonneg x

theorem sq_le_rpow_div (δ T a : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (ha : T ≤ a) : a ^ 2 ≤ a ^ (2 + δ) / T ^ δ := by
  have ha0 : 0 < a := hT.trans_le ha
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT δ)).mpr
  calc
    a ^ 2 * T ^ δ ≤ a ^ 2 * a ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT.le ha hδ.le) (sq_nonneg a)
    _ = a ^ (2 + δ) := by rw [Real.rpow_add ha0, Real.rpow_two]

theorem abs_mul_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hout : T < |x| ∨ T < |y|) :
    |x * y| ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  have hden : 0 ≤ T ^ δ := (Real.rpow_pos_of_pos hT δ).le
  by_cases hxy : |x| ≤ |y|
  · have hyT : T ≤ |y| := by
      rcases hout with hx | hy
      · exact (hx.trans_le hxy).le
      · exact hy.le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hyT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ)]
  · have hyx : |y| ≤ |x| := (lt_of_not_ge hxy).le
    have hxT : T ≤ |x| := by
      rcases hout with hx | hy
      · exact hx.le
      · exact (hy.trans_le hyx).le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
      _ ≤ |x| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |x| hδ hT hxT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg y) (2 + δ)]

theorem product_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    |x * y - trunc T x * trunc T y| ≤
      (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  by_cases hx : |x| ≤ T
  · by_cases hy : |y| ≤ T
    · simp only [trunc, hx, hy, if_true, sub_self, abs_zero]
      positivity
    · simpa [trunc, hx, hy] using
        abs_mul_tail_bound δ T x y hδ hT (Or.inr (lt_of_not_ge hy))
  · simpa [trunc, hx] using
      abs_mul_tail_bound δ T x y hδ hT (Or.inl (lt_of_not_ge hx))

theorem single_tail_bound (δ T y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    T * |y - trunc T y| ≤ |y| ^ (2 + δ) / T ^ δ := by
  by_cases hy : |y| ≤ T
  · simp only [trunc, hy, if_true, sub_self, abs_zero, mul_zero]
    positivity
  · have hTy : T ≤ |y| := (lt_of_not_ge hy).le
    simp only [trunc, hy, if_false, sub_zero]
    calc
      T * |y| ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hTy

theorem abs_mul_le_one_add_rpow (δ x y : ℝ) (hδ : 0 < δ) :
    |x * y| ≤ 1 + |x| ^ (2 + δ) + |y| ^ (2 + δ) := by
  by_cases hx : |x| ≤ 1
  · by_cases hy : |y| ≤ 1
    · have hprod : |x * y| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg x, abs_nonneg y,
          mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
      linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ),
        Real.rpow_nonneg (abs_nonneg y) (2 + δ)]
    · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
        (Or.inr (lt_of_not_ge hy))
      simp only [Real.one_rpow, div_one] at h
      linarith
  · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
      (Or.inl (lt_of_not_ge hx))
    simp only [Real.one_rpow, div_one] at h
    linarith

end MomentCovTail

open MeasureTheory ProbabilityTheory MarkovChainCLT

namespace MomentCovStationarity

theorem identDistrib_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hshift : Measurable (fun ω n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hfull : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) hshift,
    Measure.map_map (measurable_pi_apply 0) hfull] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

theorem measurable_coord {Ω : Type*} (Y : ℕ → Ω → ℝ) (s : Set ℕ)
    (i : ℕ) (hi : i ∈ s) : Measurable[processSigma Y s] (Y i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem alpha_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _

end MomentCovStationarity

open MeasureTheory ProbabilityTheory MomentCovTail
open scoped ProbabilityTheory

namespace MomentCovIntegral

theorem truncation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (δ T M a : ℝ)
    (hδ : 0 < δ) (hT : 0 < T)
    (hXm : Integrable (fun ω => |X ω| ^ (2 + δ)) P)
    (hZm : Integrable (fun ω => |Z ω| ^ (2 + δ)) P)
    (hXM : ∫ ω, |X ω| ^ (2 + δ) ∂P = M)
    (hZM : ∫ ω, |Z ω| ^ (2 + δ) ∂P = M)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hc : |cov[fun ω => trunc T (X ω), fun ω => trunc T (Z ω); P]| ≤ 4 * T ^ 2 * a) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := by
  let U := fun ω => trunc T (X ω)
  let V := fun ω => trunc T (Z ω)
  have hUm : MemLp U 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hX).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (X ω))
  have hVm : MemLp V 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hZ).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (Z ω))
  have hUi : Integrable U P := hUm.integrable (by norm_num)
  have hVi : Integrable V P := hVm.integrable (by norm_num)
  have hUV : Integrable (fun ω => U ω * V ω) P := hUm.integrable_mul hVm
  have hXZ : Integrable (fun ω => X ω * Z ω) P := by
    refine (((integrable_const (1 : ℝ)).add hXm).add hZm).mono'
      (hX.mul hZ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_mul_le_one_add_rpow δ (X ω) (Z ω) hδ
  have hZi : Integrable Z P := by
    have hzNorm : Integrable (fun ω => ‖Z ω‖ ^ (1 : ℝ)) P :=
      integrable_norm_rpow_of_le (p := 1) (q := 2 + δ) hZ.aestronglyMeasurable (by norm_num)
        (by linarith) (by linarith)
        (by simpa only [Real.norm_eq_abs] using hZm)
    have hn : Integrable (fun ω => ‖Z ω‖) P := by simpa only [Real.rpow_one] using hzNorm
    exact hn.mono' hZ.aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤
      (M + M) / T ^ δ := by
    rw [← integral_sub hXZ hUV]
    calc
      |∫ ω, X ω * Z ω - U ω * V ω ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|X ω| ^ (2 + δ) + |Z ω| ^ (2 + δ)) / T ^ δ ∂P :=
        integral_mono_ae (hXZ.sub hUV).abs ((hXm.add hZm).div_const (T ^ δ))
          (ae_of_all _ fun ω => product_tail_bound δ T (X ω) (Z ω) hδ hT)
      _ = (M + M) / T ^ δ := by rw [integral_div, integral_add hXm hZm, hXM, hZM]
  have hsingle : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [← integral_sub hZi hVi]
    calc
      T * |∫ ω, Z ω - V ω ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
      _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
      _ ≤ ∫ ω, |Z ω| ^ (2 + δ) / T ^ δ ∂P :=
        integral_mono_ae ((hZi.sub hVi).abs.const_mul T) (hZm.div_const (T ^ δ))
          (ae_of_all _ fun ω => single_tail_bound δ T (Z ω) hδ hT)
      _ = M / T ^ δ := by rw [integral_div, hZM]
  have hEV : T * |∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    simpa only [hZ0, zero_sub, abs_neg] using hsingle
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc
      |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P := integral_mono_ae hUi.abs (integrable_const T)
        (ae_of_all _ fun ω => trunc_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * a + M / T ^ δ := by
    calc
      |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
        congr 1
        simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * a + M / T ^ δ := add_le_add hc hbias
  calc
    |∫ ω, X ω * Z ω ∂P| =
        |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
      rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| :=
      abs_add_le _ _
    _ ≤ (M + M) / T ^ δ + (4 * T ^ 2 * a + M / T ^ δ) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * a + 3 * M / T ^ δ := by ring

end MomentCovIntegral

open Filter Topology

namespace MomentCovOptimize

theorem optimize (δ M a v : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (h : ∀ T : ℝ, 0 < T → v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ) :
    v ≤ (4 + 3 * M) * a ^ (δ / (2 + δ)) := by
  have hp : 0 < 2 + δ := by linarith
  have hr : 0 < δ / (2 + δ) := div_pos hδ hp
  by_cases ha0 : a = 0
  · subst a
    have hlim : Tendsto (fun T : ℝ => 3 * M / T ^ δ) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hδ).const_div_atTop (3 * M)
    have hv : v ≤ 0 := by
      apply ge_of_tendsto hlim
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simpa only [mul_zero, zero_add] using h T hT
    simpa only [Real.zero_rpow hr.ne', mul_zero] using hv
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let q : ℝ := -1 / (2 + δ)
    let r : ℝ := δ / (2 + δ)
    let T : ℝ := a ^ q
    have hT : 0 < T := Real.rpow_pos_of_pos ha' q
    have hfirst : T ^ 2 * a = a ^ r := by
      calc
        T ^ 2 * a = a ^ (q * 2) * a ^ (1 : ℝ) := by
          rw [Real.rpow_mul ha, Real.rpow_two, Real.rpow_one]
        _ = a ^ (q * 2 + 1) := (Real.rpow_add ha' _ _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          field_simp
          ring
    have hsecond : (T ^ δ)⁻¹ = a ^ r := by
      calc
        (T ^ δ)⁻¹ = (a ^ (q * δ))⁻¹ := by rw [Real.rpow_mul ha]
        _ = a ^ (-(q * δ)) := (Real.rpow_neg ha _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          ring
    calc
      v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := h T hT
      _ = (4 + 3 * M) * a ^ r := by
        rw [div_eq_mul_inv, hsecond]
        nlinarith [hfirst]
      _ = (4 + 3 * M) * a ^ (δ / (2 + δ)) := rfl

end MomentCovOptimize

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem moment_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (δ : ℝ) (hδ : 0 < δ)
    (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P) :
    ∀ k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| ≤
      (4 + 3 * ∫ ω, |Y 0 ω| ^ (2 + δ) ∂P) *
        alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ)) := by
  let M := ∫ ω, |Y 0 ω| ^ (2 + δ) ∂P
  have hM : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  intro k
  apply MomentCovOptimize.optimize δ M (alphaMixingCoef P Y (k + 1))
    (|∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) hδ hM
    (MomentCovStationarity.alpha_nonneg P Y (k + 1))
  intro T hT
  have hid := MomentCovStationarity.identDistrib_coord P Y hY hstat (k + 1)
  have hpow : Measurable (fun x : ℝ => |x| ^ (2 + δ)) := by fun_prop
  have hkm : Integrable (fun ω => |Y (k + 1) ω| ^ (2 + δ)) P :=
    (hid.comp hpow).integrable_iff.mpr hmom
  have hkM : ∫ ω, |Y (k + 1) ω| ^ (2 + δ) ∂P = M := (hid.comp hpow).integral_eq
  have hk0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  apply MomentCovIntegral.truncation_estimate P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    δ T M (alphaMixingCoef P Y (k + 1)) hδ hT hmom hkm rfl hkM hk0
  exact _root_.NumberMomentPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0
    (fun ω => MomentCovTail.trunc T (Y 0 ω))
    (fun ω => MomentCovTail.trunc T (Y (k + 1) ω))
    ((MomentCovTail.measurable_trunc T).comp
      (MomentCovStationarity.measurable_coord Y (Set.Iic 0) 0 (by simp)))
    ((MomentCovTail.measurable_trunc T).comp
      (MomentCovStationarity.measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
    T hT.le (fun ω => MomentCovTail.trunc_bound hT.le (Y 0 ω))
    (fun ω => MomentCovTail.trunc_bound hT.le (Y (k + 1) ω))



open scoped ENNReal NNReal Topology

namespace MomentApprox

open MomentCovStationarity

variable {Ω : Type*} [MeasurableSpace Ω]

lemma memLp_of_moment (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (p : ℝ) (hp : 0 < p)
    (hm : Integrable (fun ω => |X ω| ^ p) P) : MemLp X (ENNReal.ofReal p) P := by
  apply (integrable_norm_rpow_iff hX.aestronglyMeasurable (by simp [hp]) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hm

lemma moment_of_memLp (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (hX : MemLp X (ENNReal.ofReal p) P) :
    Integrable (fun ω => |X ω| ^ p) P := by
  simpa only [ENNReal.toReal_ofReal hp, Real.norm_eq_abs] using hX.integrable_norm_rpow'

lemma memLp_two_of_moment (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (δ : ℝ) (hδ : 0 < δ)
    (hm : Integrable (fun ω => |X ω| ^ (2 + δ)) P) : MemLp X 2 P := by
  apply (memLp_of_moment P X hX (2 + δ) (by linarith) hm).mono_exponent
  exact_mod_cast ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ 2 + δ by linarith)

lemma abs_integral_mul_le_second
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : MemLp X 2 P) (hZ : MemLp Z 2 P)
    (heq : ∫ ω, Z ω ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P) :
    |∫ ω, X ω * Z ω ∂P| ≤ ∫ ω, X ω ^ 2 ∂P := by
  calc |∫ ω, X ω * Z ω ∂P| ≤ ∫ ω, |X ω * Z ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (X ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
      apply integral_mono (hX.integrable_mul hZ).abs
        ((hX.integrable_sq.add hZ.integrable_sq).div_const 2)
      intro ω
      change |X ω * Z ω| ≤ (X ω ^ 2 + Z ω ^ 2) / 2
      rw [abs_mul]
      nlinarith [sq_nonneg (|X ω| - |Z ω|), sq_abs (X ω), sq_abs (Z ω)]
    _ = ∫ ω, X ω ^ 2 ∂P := by
      rw [integral_div, integral_add hX.integrable_sq hZ.integrable_sq, heq]
      ring

lemma partialSum_sq_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hs : IsStrictlyStationary P Y)
    (hc : ∫ ω, Y 0 ω ∂P = 0) (h2 : MemLp (Y 0) 2 P)
    (hcov : Summable (fun k => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|)) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) ≤
      ((∫ ω, Y 0 ω ^ 2 ∂P) + 2 * ∑' k, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) * n := by
  have hmem : ∀ i, MemLp (Y i) 2 P := fun i => (identDistrib_coord P Y hY hs i).memLp_iff.mpr h2
  have hmean : ∀ i, ∫ ω, Y i ω ∂P = 0 := fun i => (identDistrib_coord P Y hY hs i).integral_eq.trans hc
  have hsummean : ∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    simp [hmean]
  have hv := _root_.NumberMomentPort_MarkovChainCLT_variance_finsetSum_le_card_mul_of_summable_abs_cov.solution P Y hY hs hc h2 hcov (Finset.range n)
  rw [variance_eq_integral (memLp_finsetSum' _ (fun i _ => hmem i)).aemeasurable] at hv
  simpa only [Finset.sum_apply, hsummean, sub_zero, Finset.card_range, mul_comm] using hv

lemma covariance_sums_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ N i, Measurable (Z N i)) (hs : ∀ N, IsStrictlyStationary P (Z N))
    (hc : ∀ N, ∫ ω, Z N 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hZmom : ∀ N, Integrable (fun ω => |Z N 0 ω| ^ (2 + δ)) P)
    (M : ℝ) (hM : ∀ N, ∫ ω, |Z N 0 ω| ^ (2 + δ) ∂P ≤ M)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hasum : Summable (fun n => a n ^ (δ / (2 + δ))))
    (hal : ∀ N n, alphaMixingCoef P (Z N) n ≤ a n)
    (hv : Tendsto (fun N => ∫ ω, Z N 0 ω ^ 2 ∂P) atTop (𝓝 0)) :
    (∀ N, Summable (fun k => |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|)) ∧
    Tendsto (fun N => (∫ ω, Z N 0 ω ^ 2 ∂P) +
      2 * ∑' k, |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|) atTop (𝓝 0) := by
  have hp : 0 ≤ δ / (2 + δ) := by positivity
  have hM0 : 0 ≤ M := (integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)).trans (hM 0)
  let B : ℕ → ℝ := fun k => (4 + 3 * M) * a (k + 1) ^ (δ / (2 + δ))
  have hB : Summable B := (hasum.comp_injective Nat.succ_injective).mul_left (4 + 3 * M)
  let r : ℕ → ℕ → ℝ := fun N k => |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
  have hbound : ∀ N k, r N k ≤ B k := by
    intro N k
    have hh := moment_covariance_bound P (Z N) (hm N) (hs N) (hc N) δ hδ (hZmom N) k
    refine hh.trans ?_
    dsimp [B]
    apply mul_le_mul
    · linarith [hM N]
    · exact Real.rpow_le_rpow (alpha_nonneg P (Z N) (k + 1)) (hal N (k + 1)) hp
    · exact Real.rpow_nonneg (alpha_nonneg P (Z N) (k + 1)) _
    · positivity
  have hZ2 : ∀ N i, MemLp (Z N i) 2 P := fun N i =>
    (identDistrib_coord P (Z N) (hm N) (hs N) i).memLp_iff.mpr
      (memLp_two_of_moment P (Z N 0) (hm N 0) δ hδ (hZmom N))
  have hrlim : ∀ k, Tendsto (fun N => r N k) atTop (𝓝 0) := by
    intro k
    apply squeeze_zero (fun N => abs_nonneg _) (fun N => ?_) hv
    apply abs_integral_mul_le_second P _ _ (hZ2 N 0) (hZ2 N (k + 1))
    exact ((identDistrib_coord P (Z N) (hm N) (hs N) (k + 1)).comp
      (measurable_id.pow_const 2)).integral_eq
  have hrsum : ∀ N, Summable (r N) := fun N =>
    hB.of_norm_bounded (fun k => by simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k)
  have hrlim_sum : Tendsto (fun N => ∑' k, r N k) atTop (𝓝 0) := by
    have hh := tendsto_tsum_of_dominated_convergence hB hrlim
      (Filter.Eventually.of_forall (fun N k => ?_))
    · simpa using hh
    simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k
  exact ⟨hrsum, by simpa using hv.add (hrlim_sum.const_mul 2)⟩

noncomputable def high (T x : ℝ) : ℝ := if T < |x| then x else 0

lemma measurable_high (T : ℝ) : Measurable (high T) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_id measurable_const

lemma high_abs_le (T x : ℝ) : |high T x| ≤ |x| := by
  unfold high
  split_ifs <;> simp [abs_nonneg]

lemma memLp_high (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) {p : ℝ≥0∞} (hXp : MemLp X p P) (T : ℝ) :
    MemLp (fun ω => high T (X ω)) p P :=
  hXp.mono ((measurable_high T).comp hX).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using high_abs_le T (X ω))

lemma tendsto_integral_high_sq (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 P) :
    Tendsto (fun N : ℕ => ∫ ω, high (N : ℝ) (X ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => high (N : ℝ) (X ω) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro ω
    obtain ⟨K, hK⟩ := exists_nat_gt |X ω|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with N hN
    have hx : ¬ (N : ℝ) < |X ω| := by
      have hcast : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    simp [high, hx]
  have hh := tendsto_integral_of_dominated_convergence (fun ω => X ω ^ 2)
    (fun N => (((measurable_high (N : ℝ)).comp hX).pow_const 2).aestronglyMeasurable)
    hX2.integrable_sq (fun N => ae_of_all _ fun ω => ?_) hlim
  · simpa using hh
  change ‖high (N : ℝ) (X ω) ^ 2‖ ≤ X ω ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := high_abs_le (N : ℝ) (X ω)
  nlinarith [sq_abs (high (N : ℝ) (X ω)), sq_abs (X ω), abs_nonneg (high (N : ℝ) (X ω)), abs_nonneg (X ω)]

end MomentApprox

namespace MomentApprox
open MomentCovStationarity
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def centeredHigh (P : Measure Ω) (Y : ℕ → Ω → ℝ) (N i : ℕ) (ω : Ω) : ℝ :=
  high (N : ℝ) (Y i ω) - ∫ ω', high (N : ℝ) (Y 0 ω') ∂P

lemma centeredHigh_variance_control
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hs : IsStrictlyStationary P Y)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    ∃ d : ℕ → ℝ, (∀ N, 0 ≤ d N) ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ N, Summable (fun k => |∫ ω, centeredHigh P Y N 0 ω * centeredHigh P Y N (k + 1) ω ∂P|)) ∧
      ∀ N n, (∫ ω, (∑ i ∈ Finset.range n, centeredHigh P Y N i ω) ^ 2 ∂P) ≤ d N * n := by
  let p : ℝ := 2 + δ
  have hp : 0 < p := by dsimp [p]; linarith
  have hYp := memLp_of_moment P (Y 0) (hY 0) p hp hmom
  have hY2 := memLp_two_of_moment P (Y 0) (hY 0) δ hδ hmom
  have hYip : ∀ i, MemLp (Y i) (ENNReal.ofReal p) P := fun i =>
    (identDistrib_coord P Y hY hs i).memLp_iff.mpr hYp
  have hYi2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    (identDistrib_coord P Y hY hs i).memLp_iff.mpr hY2
  let m : ℕ → ℝ := fun N => ∫ ω, high (N : ℝ) (Y 0 ω) ∂P
  let g : ℕ → ℝ → ℝ := fun N x => high (N : ℝ) x - m N
  let Z := centeredHigh P Y
  have hg : ∀ N, Measurable (g N) := fun N => (measurable_high _).sub_const _
  have hZ : ∀ N i, Measurable (Z N i) := fun N i => (hg N).comp (hY i)
  have hHs : ∀ (N i : ℕ), MemLp (fun ω => high (N : ℝ) (Y i ω)) 2 P :=
    fun N i => memLp_high P (Y i) (hY i) (hYi2 i) (N : ℝ)
  have hZ2 : ∀ N i, MemLp (Z N i) 2 P := fun N i => (hHs N i).sub (memLp_const (m N))
  have hZstat : ∀ N, IsStrictlyStationary P (Z N) := fun N =>
    isStrictlyStationary_comp_of_measurable P Y hY hs (g N) (hg N)
  have hZcent : ∀ N, ∫ ω, Z N 0 ω ∂P = 0 := by
    intro N
    dsimp [Z, centeredHigh]
    rw [integral_sub ((hHs N 0).integrable (by norm_num)) (integrable_const _)]
    simp
  have hZα : ∀ N k, alphaMixingCoef P (Z N) k ≤ alphaMixingCoef P Y k := fun N k =>
    (alphaMixingCoef_comp_nonneg_le_of_finite P Y (g N) (hg N) k).2
  let C : ℝ := ∫ ω, |Y 0 ω| ∂P
  have hC0 : 0 ≤ C := integral_nonneg fun ω => abs_nonneg _
  have hm : ∀ N, |m N| ≤ C := by
    intro N
    exact abs_integral_le_integral_abs.trans
      (integral_mono ((hHs N 0).integrable (by norm_num)).abs
        (hY2.integrable (by norm_num)).abs (fun ω => high_abs_le (N : ℝ) (Y 0 ω)))
  let W : Ω → ℝ := fun ω => |Y 0 ω| + C
  have hWp : MemLp W (ENNReal.ofReal p) P := by
    convert hYp.norm.add (memLp_const C) using 1 <;>
      first | rfl | (funext ω; simp [W, Real.norm_eq_abs])
  have hWmom : Integrable (fun ω => |W ω| ^ p) P := moment_of_memLp P W p hp.le hWp
  have henv : ∀ N ω, |Z N 0 ω| ≤ |W ω| := by
    intro N ω
    rw [abs_of_nonneg (show 0 ≤ W ω from add_nonneg (abs_nonneg _) hC0)]
    calc |Z N 0 ω| ≤ |high (N : ℝ) (Y 0 ω)| + |m N| := by
          simpa only [Z, centeredHigh, m, sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (high (N : ℝ) (Y 0 ω)) 0 (m N))
      _ ≤ W ω := add_le_add (high_abs_le (N : ℝ) (Y 0 ω)) (hm N)
  have hZp : ∀ N, MemLp (Z N 0) (ENNReal.ofReal p) P := fun N =>
    ((memLp_high P (Y 0) (hY 0) hYp (N : ℝ)).sub (memLp_const (m N)))
  have hZmom : ∀ N, Integrable (fun ω => |Z N 0 ω| ^ (2 + δ)) P := fun N =>
    moment_of_memLp P (Z N 0) p hp.le (hZp N)
  have hZM : ∀ N, (∫ ω, |Z N 0 ω| ^ (2 + δ) ∂P) ≤ ∫ ω, |W ω| ^ p ∂P := fun N =>
    integral_mono (hZmom N) hWmom (fun ω => Real.rpow_le_rpow (abs_nonneg _) (henv N ω) hp.le)
  have hvle : ∀ N, (∫ ω, Z N 0 ω ^ 2 ∂P) ≤ ∫ ω, high (N : ℝ) (Y 0 ω) ^ 2 ∂P := by
    intro N
    change (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) ≤ _
    rw [show (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) =
      Var[fun ω => high (N : ℝ) (Y 0 ω); P] from
        (variance_eq_integral ((measurable_high (N : ℝ)).comp (hY 0)).aemeasurable).symm]
    exact variance_le_expectation_sq ((measurable_high (N : ℝ)).comp (hY 0)).aestronglyMeasurable
  have hvlim : Tendsto (fun N => ∫ ω, Z N 0 ω ^ 2 ∂P) atTop (𝓝 0) :=
    squeeze_zero (fun N => integral_nonneg fun ω => sq_nonneg _) hvle
      (tendsto_integral_high_sq P (Y 0) (hY 0) hY2)
  obtain ⟨hcov, hlim⟩ := covariance_sums_tendsto_zero P Z hZ hZstat hZcent δ hδ hZmom
    (∫ ω, |W ω| ^ p ∂P) hZM (alphaMixingCoef P Y) (alpha_nonneg P Y) hα hZα hvlim
  let d : ℕ → ℝ := fun N => (∫ ω, Z N 0 ω ^ 2 ∂P) +
    2 * ∑' k, |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
  refine ⟨d, ?_, hlim, hcov, ?_⟩
  · intro N
    exact add_nonneg (integral_nonneg fun ω => sq_nonneg _)
      (mul_nonneg (by norm_num) (tsum_nonneg fun k => abs_nonneg _))
  · intro N n
    exact partialSum_sq_le P (Z N) (hZ N) (hZstat N) (hZcent N) (hZ2 N 0) (hcov N) n

end MomentApprox

namespace MomentApprox
variable {Ω : Type*} [MeasurableSpace Ω]

lemma sq_difference_young (x y η : ℝ) (hη : 0 < η) :
    |x ^ 2 - y ^ 2| ≤ (η ^ 2 * x ^ 2 + (1 + η) * (x - y) ^ 2) / η := by
  rw [le_div_iff₀ hη]
  rw [show |x ^ 2 - y ^ 2| * η = |(x ^ 2 - y ^ 2) * η| by rw [abs_mul, abs_of_pos hη]]
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (η * x + (x - y))]
  · nlinarith [sq_nonneg (η * x - (x - y)), mul_nonneg hη.le (sq_nonneg (x-y))]

lemma integral_sq_difference_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : Ω → ℝ) (hF : MemLp F 2 P) (hG : MemLp G 2 P) (η : ℝ) (hη : 0 < η) :
    |(∫ ω, F ω ^ 2 ∂P) - ∫ ω, G ω ^ 2 ∂P| ≤
      η * (∫ ω, F ω ^ 2 ∂P) + (1 + 1 / η) * ∫ ω, (F ω - G ω) ^ 2 ∂P := by
  have hD : Integrable (fun ω => (F ω - G ω) ^ 2) P := (hF.sub hG).integrable_sq
  rw [← integral_sub hF.integrable_sq hG.integrable_sq]
  calc |∫ ω, F ω ^ 2 - G ω ^ 2 ∂P| ≤ ∫ ω, |F ω ^ 2 - G ω ^ 2| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (η ^ 2 * F ω ^ 2 + (1 + η) * (F ω - G ω) ^ 2) / η ∂P := by
      apply integral_mono (hF.integrable_sq.sub hG.integrable_sq).abs
        (((hF.integrable_sq.const_mul _).add (hD.const_mul _)).div_const _)
      exact fun ω => sq_difference_young _ _ η hη
    _ = _ := by
      rw [integral_div, integral_add (hF.integrable_sq.const_mul _) (hD.const_mul _),
        integral_const_mul, integral_const_mul]
      field_simp
      ring

lemma limits_second_moments_tendsto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (G : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ n, MemLp (F n) 2 P) (hG : ∀ N n, MemLp (G N n) 2 P)
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (herr : ∀ N n, (∫ ω, (F n ω - G N n ω) ^ 2 ∂P) ≤ d N)
    (s : ℝ) (hs : 0 < s) (sG : ℕ → ℝ)
    (hFlim : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂P) atTop (𝓝 s))
    (hGlim : ∀ N, Tendsto (fun n => ∫ ω, G N n ω ^ 2 ∂P) atTop (𝓝 (sG N))) :
    Tendsto sG atTop (𝓝 s) := by
  have hb : ∀ (N : ℕ) (η : ℝ), 0 < η →
      |s - sG N| ≤ η * s + (1 + 1 / η) * d N := by
    intro N η hη
    apply le_of_tendsto_of_tendsto ((hFlim.sub (hGlim N)).abs)
      ((hFlim.const_mul η).add_const ((1 + 1 / η) * d N))
    apply Filter.Eventually.of_forall
    intro n
    exact (integral_sq_difference_le P _ _ (hF n) (hG N n) η hη).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (herr N n)
        (show 0 ≤ 1 + 1 / η by positivity)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (2 * (s + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have heta : η * (s + 1) = ε / 2 := by dsimp [η]; field_simp
  have hηs : η * s < ε / 2 := by nlinarith
  have ht : Tendsto (fun N => (1 + 1 / η) * d N) atTop (𝓝 0) := by
    simpa using hd.const_mul (1 + 1 / η)
  have hh : ∀ᶠ N in atTop, (1 + 1 / η) * d N < ε / 2 :=
    ht.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hh] with N hN
  rw [Real.dist_eq, abs_sub_comm]
  exact (hb N η hη).trans_lt (by linarith)

lemma norm_cexp_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤ |x - y| := by
  calc ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖
      = ‖(Complex.exp ((x-y) * Complex.I) - 1) * Complex.exp (y * Complex.I)‖ := by
        congr 1
        rw [sub_mul, one_mul, ← Complex.exp_add]
        congr 2 <;> push_cast <;> ring
    _ = ‖Complex.exp ((x-y) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ |x-y| := by
      simpa only [mul_comm, Real.norm_eq_abs, Complex.ofReal_sub] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

noncomputable def phase (t x : ℝ) : ℂ := Complex.exp ((t*x : ℝ) * Complex.I)

lemma norm_phase_sub_le (t x y : ℝ) : ‖phase t x - phase t y‖ ≤ |t| * |x-y| := by
  simpa only [phase, ← mul_sub, abs_mul] using norm_cexp_mul_I_sub_le (t*x) (t*y)

lemma measurable_phase (t : ℝ) : Measurable (phase t) := by unfold phase; fun_prop

lemma norm_phase (t x : ℝ) : ‖phase t x‖ = 1 := Complex.norm_exp_ofReal_mul_I (t*x)

lemma integral_abs_le_sqrt (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → ℝ)
    (hF : MemLp F 2 P) : (∫ ω, |F ω| ∂P) ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂P) := by
  have hv := variance_nonneg (fun ω => ‖F ω‖) P
  rw [variance_eq_sub hF.norm] at hv
  simp only [Pi.pow_apply, Real.norm_eq_abs, sq_abs] at hv
  have hs := Real.sq_sqrt (integral_nonneg (μ := P) fun ω => sq_nonneg (F ω))
  have hroot := Real.sqrt_nonneg (∫ ω, F ω ^ 2 ∂P)
  nlinarith

lemma charFun_map_eq_integral_phase (P : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (t : ℝ) :
    charFun (P.map F) t = ∫ ω, phase t (F ω) ∂P := by
  rw [charFun_apply_real, integral_map hF.aemeasurable (by fun_prop)]
  simp only [phase, Complex.ofReal_mul]

lemma charFun_diff_le_sqrt (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun ω => F ω - G ω) 2 P) (t : ℝ) :
    ‖charFun (P.map F) t - charFun (P.map G) t‖ ≤
      |t| * Real.sqrt (∫ ω, (F ω - G ω) ^ 2 ∂P) := by
  have hFi : Integrable (fun ω => phase t (F ω)) P :=
    Integrable.of_bound ((measurable_phase t).comp hF).aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_phase t (F ω)).le)
  have hGi : Integrable (fun ω => phase t (G ω)) P :=
    Integrable.of_bound ((measurable_phase t).comp hG).aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_phase t (G ω)).le)
  rw [charFun_map_eq_integral_phase P F hF t, charFun_map_eq_integral_phase P G hG t,
    ← integral_sub hFi hGi]
  calc ‖∫ ω, phase t (F ω) - phase t (G ω) ∂P‖
      ≤ ∫ ω, ‖phase t (F ω) - phase t (G ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |F ω - G ω| ∂P := by
      apply integral_mono (hFi.sub hGi).norm (((hD.integrable (by norm_num)).abs).const_mul _)
      exact fun ω => norm_phase_sub_le t (F ω) (G ω)
    _ = |t| * ∫ ω, |F ω - G ω| ∂P := integral_const_mul _ _
    _ ≤ |t| * Real.sqrt (∫ ω, (F ω - G ω) ^ 2 ∂P) :=
      mul_le_mul_of_nonneg_left (integral_abs_le_sqrt P _ hD) (abs_nonneg _)

end MomentApprox

namespace MomentApprox
variable {Ω : Type*} [MeasurableSpace Ω]

lemma charFun_tendsto_of_L2_approx
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (G : ℕ → ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n)) (hGm : ∀ N n, Measurable (G N n))
    (hF : ∀ n, MemLp (F n) 2 P) (hG : ∀ N n, MemLp (G N n) 2 P)
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (herr : ∀ N n, (∫ ω, (F n ω - G N n ω) ^ 2 ∂P) ≤ d N)
    (s : ℝ) (hs : 0 < s) (sG : ℕ → ℝ)
    (hFlim : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂P) atTop (𝓝 s))
    (hGlim : ∀ N, Tendsto (fun n => ∫ ω, G N n ω ^ 2 ∂P) atTop (𝓝 (sG N)))
    (hGlaw : ∀ N, 0 < sG N → ∀ t : ℝ,
      Tendsto (fun n => charFun (P.map (G N n)) t) atTop
        (𝓝 (charFun (gaussianReal 0 (sG N).toNNReal) t))) :
    ∀ t : ℝ, Tendsto (fun n => charFun (P.map (F n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 s.toNNReal) t)) := by
  have hsig := limits_second_moments_tendsto P F G hF hG d hd herr s hs sG hFlim hGlim
  intro t
  have hgaussCont : Continuous (fun v : ℝ => charFun (gaussianReal 0 v.toNNReal) t) := by
    simp only [charFun_gaussianReal]
    fun_prop
  have hgauss := hgaussCont.continuousAt.tendsto.comp hsig
  have herror : Tendsto (fun N => |t| * Real.sqrt (d N)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hd).const_mul |t|
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have h1 : ∀ᶠ N in atTop, |t| * Real.sqrt (d N) < ε / 3 :=
    herror.eventually (gt_mem_nhds hε3)
  have h2 : ∀ᶠ N in atTop,
      dist (charFun (gaussianReal 0 (sG N).toNNReal) t)
        (charFun (gaussianReal 0 s.toNNReal) t) < ε / 3 :=
    Metric.tendsto_nhds.mp hgauss (ε / 3) hε3
  have h3 : ∀ᶠ N in atTop, 0 < sG N := hsig.eventually (lt_mem_nhds hs)
  obtain ⟨N, hN1, hN2, hN3⟩ := (h1.and (h2.and h3)).exists
  have hfixed := Metric.tendsto_nhds.mp (hGlaw N hN3 t) (ε / 3) hε3
  filter_upwards [hfixed] with n hn
  have herrCF : dist (charFun (P.map (F n)) t) (charFun (P.map (G N n)) t) < ε / 3 := by
    rw [dist_eq_norm]
    exact ((charFun_diff_le_sqrt P _ _ (hFm n) (hGm N n) ((hF n).sub (hG N n)) t).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (herr N n)) (abs_nonneg _))).trans_lt hN1
  have htri := dist_triangle (charFun (P.map (F n)) t) (charFun (P.map (G N n)) t)
    (charFun (gaussianReal 0 s.toNNReal) t)
  have htri2 := dist_triangle (charFun (P.map (G N n)) t)
    (charFun (gaussianReal 0 (sG N).toNNReal) t) (charFun (gaussianReal 0 s.toNNReal) t)
  linarith

lemma normalized_integral_sq (P : Measure Ω) (H : Ω → ℝ) (n : ℕ) :
    (∫ ω, ((Real.sqrt n)⁻¹ * H ω) ^ 2 ∂P) = (n : ℝ)⁻¹ * ∫ ω, H ω ^ 2 ∂P := by
  simp_rw [mul_pow]
  rw [integral_const_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma low_add_high (T x : ℝ) : MomentCovTail.trunc T x + high T x = x := by
  by_cases h : |x| ≤ T
  · simp [MomentCovTail.trunc, high, h, not_lt.mpr h]
  · simp [MomentCovTail.trunc, high, h, lt_of_not_ge h]

end MomentApprox
open MomentApprox MomentCovStationarity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ))))
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ =>
          charFun (P.map (fun ω =>
            (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)) t)
        atTop (𝓝 (charFun (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) t)) := by
  have hY02 := memLp_two_of_moment P (Y 0) (hY 0) δ hδ hmom
  have hYi2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    (identDistrib_coord P Y hY hstat i).memLp_iff.mpr hY02
  let m : ℕ → ℝ := fun N => ∫ ω, high (N : ℝ) (Y 0 ω) ∂P
  let Z := centeredHigh P Y
  let g : ℕ → ℝ → ℝ := fun N x => x - (high (N : ℝ) x - m N)
  let X : ℕ → ℕ → Ω → ℝ := fun N i ω => g N (Y i ω)
  have hg : ∀ N, Measurable (g N) := fun N =>
    measurable_id.sub ((measurable_high _).sub_const _)
  have hXm : ∀ N i, Measurable (X N i) := fun N i => (hg N).comp (hY i)
  have hXs : ∀ N, IsStrictlyStationary P (X N) := fun N =>
    isStrictlyStationary_comp_of_measurable P Y hY hstat (g N) (hg N)
  have hHigh2 : ∀ (N i : ℕ), MemLp (fun ω => high (N : ℝ) (Y i ω)) 2 P := fun N i =>
    memLp_high P (Y i) (hY i) (hYi2 i) (N : ℝ)
  have hZ2 : ∀ N i, MemLp (Z N i) 2 P := fun N i => (hHigh2 N i).sub (memLp_const (m N))
  have hX2 : ∀ N i, MemLp (X N i) 2 P := fun N i => (hYi2 i).sub (hZ2 N i)
  have hZ0 : ∀ N, ∫ ω, Z N 0 ω ∂P = 0 := by
    intro N
    dsimp [Z, centeredHigh]
    rw [integral_sub ((hHigh2 N 0).integrable (by norm_num)) (integrable_const _)]
    simp
  have hX0 : ∀ N, ∫ ω, X N 0 ω ∂P = 0 := by
    intro N
    change (∫ ω, Y 0 ω - Z N 0 ω ∂P) = 0
    rw [integral_sub (hY02.integrable (by norm_num)) ((hZ2 N 0).integrable (by norm_num)), hcent, hZ0]
    simp
  let B : ℕ → ℝ := fun N => N + |m N| + 1
  have hBound : ∀ N i ω, |X N i ω| < B N := by
    intro N i ω
    have heq : X N i ω = MomentCovTail.trunc (N : ℝ) (Y i ω) + m N := by
      have hh := low_add_high (N : ℝ) (Y i ω)
      dsimp [X, g]
      linarith
    rw [heq]
    calc |MomentCovTail.trunc (N : ℝ) (Y i ω) + m N|
        ≤ |MomentCovTail.trunc (N : ℝ) (Y i ω)| + |m N| := abs_add_le _ _
      _ ≤ (N : ℝ) + |m N| := add_le_add
        (MomentCovTail.trunc_bound (Nat.cast_nonneg N) (Y i ω)) le_rfl
      _ < B N := by dsimp [B]; linarith
  have hαbase : Summable (fun n => alphaMixingCoef P Y n) := by
    apply Summable.of_nonneg_of_le (alpha_nonneg P Y) (fun n => ?_) hα
    apply Real.self_le_rpow_of_le_one (alpha_nonneg P Y n)
      ((_root_.NumberMomentPort_MarkovChainCLT_alphaMixingCoef_le_quarter.solution P Y hY n).trans (by norm_num))
    apply (div_le_one (show 0 < 2 + δ by linarith)).mpr
    linarith
  have hXα : ∀ N, Summable (fun n => alphaMixingCoef P (X N) n) := by
    intro N
    exact Summable.of_nonneg_of_le (alpha_nonneg P (X N))
      (fun n => (alphaMixingCoef_comp_nonneg_le_of_finite P Y (g N) (hg N) n).2) hαbase
  have hXcov : ∀ N, Summable (fun k => ∫ ω, X N 0 ω * X N (k + 1) ω ∂P) := fun N =>
    _root_.NumberMomentPort_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha.solution P (X N) (hXm N) (hXs N) (hX0 N)
      (B N) (fun i => ae_of_all _ (hBound N i)) (hXα N)
  obtain ⟨d, hd0, hdlim, hZcov, hdvar⟩ := centeredHigh_variance_control P Y hY hstat δ hδ hmom hα
  let F : ℕ → Ω → ℝ := fun n ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω
  let G : ℕ → ℕ → Ω → ℝ := fun N n ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, X N i ω
  have hFm : ∀ n, Measurable (F n) := fun n =>
    (Finset.measurable_sum _ (fun i _ => hY i)).const_mul _
  have hGm : ∀ N n, Measurable (G N n) := fun N n =>
    (Finset.measurable_sum _ (fun i _ => hXm N i)).const_mul _
  have hF2 : ∀ n, MemLp (F n) 2 P := fun n =>
    (memLp_finsetSum _ (fun i _ => hYi2 i)).const_mul _
  have hG2 : ∀ N n, MemLp (G N n) 2 P := fun N n =>
    (memLp_finsetSum _ (fun i _ => hX2 N i)).const_mul _
  have hdiff : ∀ N n ω, F n ω - G N n ω =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Z N i ω := by
    intro N n ω
    dsimp [F, G]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [X, g, Z, centeredHigh, m]
    ring
  have herr : ∀ N n, (∫ ω, (F n ω - G N n ω) ^ 2 ∂P) ≤ d N := by
    intro N n
    simp_rw [hdiff]
    rw [normalized_integral_sq]
    by_cases hn : n = 0
    · simpa [hn] using hd0 N
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    calc (n : ℝ)⁻¹ * (∫ ω, (∑ i ∈ Finset.range n, Z N i ω) ^ 2 ∂P)
        ≤ (n : ℝ)⁻¹ * (d N * n) :=
          mul_le_mul_of_nonneg_left (hdvar N n) (by positivity)
      _ = d N := by field_simp
  have hFlim : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P Y)) := by
    simpa only [F, normalized_integral_sq] using
      _root_.NumberMomentPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum.solution P Y hY hstat hY02 hsum
  have hGlim : ∀ N, Tendsto (fun n => ∫ ω, G N n ω ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P (X N))) := by
    intro N
    simpa only [G, normalized_integral_sq] using
      _root_.NumberMomentPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum.solution P (X N) (hXm N) (hXs N) (hX2 N 0) (hXcov N)
  apply charFun_tendsto_of_L2_approx P F G hFm hGm hF2 hG2 d hdlim herr
    (seqAsymptoticVariance P Y) hvar (fun N => seqAsymptoticVariance P (X N)) hFlim hGlim
  intro N hN t
  have hdist := _root_.NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha.solution P (X N) (hXm N) (hXs N)
    (hX0 N) (B N) (fun i => ae_of_all _ (hBound N i)) (hXα N) (hXcov N) hN
  have hh := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hdist.tendsto) t
  simpa only [Measure.map_id, ProbabilityMeasure.coe_mk, G] using hh

end NumberMomentPort_MarkovChainCLT_charFun_tendsto_of_alpha_pow_summable


namespace NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_alpha_pow_summable

/-!
Reduction of the Ibragimov-Linnik moment-case CLT (Jones 2004, Theorem 5,
condition 2, eq. (10)) to characteristic-function convergence.

The only platform input is `_root_.NumberMomentPort_MarkovChainCLT_charFun_tendsto_of_alpha_pow_summable.solution`;
the conclusion follows by Lévy's continuity theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`), which Mathlib
proves through Prokhorov's theorem. This is the same two-step structure Mathlib
uses for the classical iid CLT (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

open MarkovChainCLT

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ))))
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  -- The normalised partial sums are measurable, so their laws are probability measures.
  have hmX : ∀ (n : ℕ), Measurable (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω) := by
    intro n
    refine Measurable.mul measurable_const ?_
    exact Finset.measurable_sum _ fun i _ => hY i
  refine ⟨fun n => ((hmX n).aemeasurable : AEMeasurable _ P), measurable_id.aemeasurable, ?_⟩
  -- Lévy's continuity theorem turns characteristic-function convergence into weak
  -- convergence of the laws.
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
  intro t
  simpa only [Measure.map_id, ProbabilityMeasure.coe_mk] using
    _root_.NumberMomentPort_MarkovChainCLT_charFun_tendsto_of_alpha_pow_summable.solution P Y hY hstat hcent δ hδ hmom hα hsum hvar t

end NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_alpha_pow_summable

section OwnCandidate

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 5, condition 2 (Ibragimov–Linnik moment case), reduced to the
covariance-summability and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := _root_.NumberMomentPort_MarkovChainCLT_summable_covariance_of_alpha_pow_summable.solution
    P Y hY hstat hcent δ hδ hmom hα
  refine ⟨hsum, fun hvar => ?_⟩
  exact _root_.NumberMomentPort_MarkovChainCLT_tendstoInDistribution_of_alpha_pow_summable.solution
    P Y hY hstat hcent δ hδ hmom hα hsum hvar

end OwnCandidate
#print axioms solution