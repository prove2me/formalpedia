-- Prove2me | solution 1 for MarkovChainCLT.clt_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:23:50.525966+00:00
-- url     : https://prove2.me/submissions/a66f1edb-132b-4a5e-9dbf-e7d012f02416

import Definitions.Def_MixingCoefficients
import Mathlib
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NumberLogPort_LayerCake_bounded_layercake_identity

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

end NumberLogPort_LayerCake_bounded_layercake_identity


namespace NumberLogPort_LayerCake_expectation_add_const

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
    fun ω => _root_.NumberLogPort_LayerCake_bounded_layercake_identity.solution (W ω) M (hWb ω)
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

end NumberLogPort_LayerCake_expectation_add_const


namespace NumberLogPort_ProbabilityTheory_cov_indicator_eq

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

end NumberLogPort_ProbabilityTheory_cov_indicator_eq


namespace NumberLogPort_MarkovChainCLT_processSigma_le_of_measurable

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

end NumberLogPort_MarkovChainCLT_processSigma_le_of_measurable


namespace NumberLogPort_MarkovChainCLT_alpha_indicator_cov_le

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

end NumberLogPort_MarkovChainCLT_alpha_indicator_cov_le


namespace NumberLogPort_MarkovChainCLT_alpha_cov_bounded

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
    _root_.NumberLogPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberLogPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
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
    fun t s => _root_.NumberLogPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y n k _ _ (hAt t) (hBs s)
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
    fun ω => _root_.NumberLogPort_LayerCake_bounded_layercake_identity.solution (U ω) M (hUb ω)
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
    _root_.NumberLogPort_LayerCake_expectation_add_const.solution P V hVm M (fun ω => hVb ω)
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
      _root_.NumberLogPort_LayerCake_bounded_layercake_identity.solution (V ω) M (hVb ω)
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
    rw [norm_mul]
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
      rw [norm_mul]
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
      _root_.NumberLogPort_ProbabilityTheory_cov_indicator_eq.solution P _ _ (hAt_amb q.1) (hBs_amb q.2)
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


end NumberLogPort_MarkovChainCLT_alpha_cov_bounded


namespace NumberLogPort_MeasureTheory_uniformIntegrable_one_of_sq_bounded_approx

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz: the integral of a nonnegative `L²` function over a set is bounded by the
`L²` norm times the square root of the measure of the set. -/
private theorem setIntegral_le_sqrt_mul_sqrt_measure (P : Measure Ω) [IsProbabilityMeasure P] (u : Ω → ℝ)
    (hu0 : ∀ ω, 0 ≤ u ω) (hu2 : MemLp u 2 P) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ ω in s, u ω ∂P ≤ Real.sqrt (∫ ω, (u ω) ^ 2 ∂P) * Real.sqrt (P s).toReal := by
  have hind : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 P := (memLp_const (1 : ℝ)).indicator hs
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
    (f := u) (g := s.indicator (fun _ => (1 : ℝ)))
    (Eventually.of_forall fun ω => hu0 ω)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (by simpa [ENNReal.ofReal_ofNat] using hu2) (by simpa [ENNReal.ofReal_ofNat] using hind)
  have hlhs : ∫ ω, u ω * s.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω in s, u ω ∂P := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases h : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hpow : ∀ g : Ω → ℝ, (∫ ω, g ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ ω, (g ω) ^ 2 ∂P) := by
    intro g
    have h : ∫ ω, g ω ^ (2 : ℝ) ∂P = ∫ ω, (g ω) ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp
    rw [h, Real.sqrt_eq_rpow]
  rw [hlhs, hpow u, hpow _] at h2
  have e2 : ∫ ω, (s.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂P = (P s).toReal := by
    have h : ∀ ω, (s.indicator (fun _ => (1 : ℝ)) ω) ^ 2 = s.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω; by_cases h : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    simp only [h]
    rw [integral_indicator hs]
    simp [measureReal_def]
  rwa [e2] at h2

/-- For a nonnegative integrable function the integral over `{g ≥ D}` is arbitrarily small once
the threshold `D` is large. -/
private theorem exists_tail_setIntegral_le (P : Measure Ω) (g : Ω → ℝ)
    (hg : Integrable g P) (hgm : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, C ≤ D → ∫ ω in {ω | D ≤ g ω}, g ω ∂P ≤ ε := by
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) ≤ g ω} :=
    fun k => measurableSet_le measurable_const hgm
  have htend : Tendsto (fun k : ℕ => ∫ ω, Set.indicator {ω | (k : ℝ) ≤ g ω} g ω ∂P)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (F := fun (k : ℕ) ω =>
        Set.indicator {ω | (k : ℝ) ≤ g ω} g ω) (f := fun _ => (0 : ℝ)) (bound := g) (l := atTop)
      (Eventually.of_forall fun k => (hg.indicator (hmeas k)).aestronglyMeasurable)
      (Eventually.of_forall fun k => Eventually.of_forall fun ω => by
        rcases Set.indicator_eq_zero_or_self {ω | (k : ℝ) ≤ g ω} g ω with h | h
        · simp [h, hg0 ω]
        · simp [h, abs_of_nonneg (hg0 ω)])
      hg
      (Eventually.of_forall fun ω => ?_)
    · simpa using h
    · obtain ⟨k, hk⟩ := exists_nat_gt (g ω)
      refine tendsto_atTop_of_eventually_const (i₀ := k) fun j hj => ?_
      have hne : ¬ ((j : ℝ) ≤ g ω) := by
        have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      simp [Set.indicator_of_notMem, hne]
  obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  refine ⟨max 1 k, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun D hD => ?_⟩
  have hsub : {ω | D ≤ g ω} ⊆ {ω | (k : ℝ) ≤ g ω} := fun ω hω =>
    le_trans (le_trans (le_max_right 1 (k : ℝ)) hD) hω
  calc ∫ ω in {ω | D ≤ g ω}, g ω ∂P ≤ ∫ ω in {ω | (k : ℝ) ≤ g ω}, g ω ∂P :=
        setIntegral_mono_set hg.integrableOn (Eventually.of_forall hg0)
          (HasSubset.Subset.eventuallyLE hsub)
    _ = ∫ ω, Set.indicator {ω | (k : ℝ) ≤ g ω} g ω ∂P := (integral_indicator (hmeas k)).symm
    _ ≤ ε := le_of_lt hk

/-- The `L¹`-seminorm of the restriction of a nonnegative integrable function to a measurable
set is the (real) integral over that set. -/
private theorem eLpNorm_one_indicator_eq_ofReal_setIntegral (P : Measure Ω) (g : Ω → ℝ)
    (hg : Integrable g P) (hg0 : ∀ ω, 0 ≤ g ω) {s : Set Ω} (hs : MeasurableSet s) :
    eLpNorm (s.indicator g) 1 P = ENNReal.ofReal (∫ ω in s, g ω ∂P) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_indicator hs,
    ofReal_integral_eq_lintegral_ofReal (hg.indicator hs)
      (Eventually.of_forall fun ω => Set.indicator_nonneg (fun x _ => hg0 x) ω)]
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal (Set.indicator_nonneg (fun x _ => hg0 x) ω)]


end Helpers

theorem solution {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hfm : ∀ n, Measurable (f n)) (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfint : ∀ n, Integrable (f n) P) (hfle : ∀ n, ∫ ω, f n ω ∂P ≤ 1)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ u w : ℕ → Ω → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, N ≤ n → MemLp (u n) 2 P) ∧ (∀ n, N ≤ n → Integrable (w n) P) ∧
      (∀ n, N ≤ n → ∀ ω, 0 ≤ u n ω) ∧ (∀ n, N ≤ n → ∀ ω, 0 ≤ w n ω) ∧
      (∀ n, N ≤ n → ∀ ω, f n ω ≤ u n ω + w n ω) ∧
      (∀ n, N ≤ n → ∫ ω, (u n ω) ^ 2 ∂P ≤ M) ∧
      (∀ n, N ≤ n → ∫ ω, w n ω ∂P ≤ ε)) :
    UniformIntegrable f 1 P := by
  refine uniformIntegrable_of (le_refl 1) (by simp)
    (fun n => (hfm n).aestronglyMeasurable) ?_
  intro ε hε
  obtain ⟨N, u, w, M, hM0, hu2, hwint, hu0, hw0, hle, huM, hwε⟩ := hdec (ε / 2) (by linarith)
  choose Cn hCn0 hCnb using fun n =>
    exists_tail_setIntegral_le P (f n) (hfint n) (hfm n) (fun ω => hf0 n ω) hε
  set C : ℝ := max (4 * M / ε ^ 2 + 1) (∑ k ∈ Finset.range N, Cn k) with hC
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCbig : 4 * M / ε ^ 2 + 1 ≤ C := le_max_left _ _
  have hCsmall : ∀ n, n < N → Cn n ≤ C := by
    intro n hn
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f := Cn) (fun k _ => (hCn0 k).le) (Finset.mem_range.2 hn)
  refine ⟨C.toNNReal, fun n => ?_⟩
  have hCcoe : ((C.toNNReal : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hCpos.le
  have hset : {x | C.toNNReal ≤ ‖f n x‖₊} = {ω | C ≤ f n ω} := by
    ext x
    simp only [Set.mem_setOf_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, hCcoe,
      abs_of_nonneg (hf0 n x)]
  have hsmeas : MeasurableSet {ω | C ≤ f n ω} := measurableSet_le measurable_const (hfm n)
  rw [hset, eLpNorm_one_indicator_eq_ofReal_setIntegral P (f n) (hfint n) (hf0 n) hsmeas]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hn : N ≤ n
  · -- the interesting range: split into the `L²`-bounded part and the small part
    have huint : Integrable (u n) P := (hu2 n hn).integrable (by norm_num)
    have hsum_int : Integrable (fun ω => u n ω + w n ω) P := huint.add (hwint n hn)
    have hstep1 : ∫ ω in {ω | C ≤ f n ω}, f n ω ∂P
        ≤ ∫ ω in {ω | C ≤ f n ω}, (u n ω + w n ω) ∂P := by
      refine setIntegral_mono_on (hfint n).integrableOn hsum_int.integrableOn hsmeas ?_
      intro ω _
      exact hle n hn ω
    have hstep2 : ∫ ω in {ω | C ≤ f n ω}, (u n ω + w n ω) ∂P
        = (∫ ω in {ω | C ≤ f n ω}, u n ω ∂P) + ∫ ω in {ω | C ≤ f n ω}, w n ω ∂P :=
      integral_add huint.integrableOn (hwint n hn).integrableOn
    -- the tail part is small in `L¹`
    have hwbound : ∫ ω in {ω | C ≤ f n ω}, w n ω ∂P ≤ ε / 2 := by
      refine le_trans ?_ (hwε n hn)
      refine setIntegral_le_integral (hwint n hn) ?_
      exact Eventually.of_forall fun ω => hw0 n hn ω
    -- the bounded part is controlled by Cauchy–Schwarz and Markov's inequality
    have hmarkov : C * (P {ω | C ≤ f n ω}).toReal ≤ 1 := by
      refine le_trans ?_ (hfle n)
      simpa [measureReal_def] using
        mul_meas_ge_le_integral_of_nonneg (μ := P)
          (Eventually.of_forall fun ω => hf0 n ω) (hfint n) C
    have hmeasle : (P {ω | C ≤ f n ω}).toReal ≤ 1 / C := by
      rw [le_div_iff₀ hCpos]
      linarith [hmarkov]
    have hcs := setIntegral_le_sqrt_mul_sqrt_measure P (u n) (hu0 n hn) (hu2 n hn) hsmeas
    have hsqrtM : Real.sqrt (∫ ω, (u n ω) ^ 2 ∂P) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (huM n hn)
    have hsqrtmeas : Real.sqrt (P {ω | C ≤ f n ω}).toReal ≤ Real.sqrt (1 / C) :=
      Real.sqrt_le_sqrt hmeasle
    have hubound : ∫ ω in {ω | C ≤ f n ω}, u n ω ∂P ≤ Real.sqrt M * Real.sqrt (1 / C) := by
      refine hcs.trans (mul_le_mul hsqrtM hsqrtmeas (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hfinal : Real.sqrt M * Real.sqrt (1 / C) ≤ ε / 2 := by
      have hMC : M / C ≤ (ε / 2) ^ 2 := by
        rw [div_le_iff₀ hCpos]
        have h1 : 4 * M / ε ^ 2 ≤ C := by linarith
        have h2 : 4 * M ≤ C * ε ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at h1
          linarith
        nlinarith [sq_nonneg ε]
      have : Real.sqrt M * Real.sqrt (1 / C) = Real.sqrt (M / C) := by
        rw [← Real.sqrt_mul hM0]
        ring_nf
      rw [this]
      calc Real.sqrt (M / C) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt hMC
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    linarith [hstep1, hstep2.le, hstep2.ge, hubound, hwbound, hfinal]
  · -- finitely many exceptional indices, each handled by integrability
    exact hCnb n C (hCsmall n (lt_of_not_ge hn))

end NumberLogPort_MeasureTheory_uniformIntegrable_one_of_sq_bounded_approx


namespace NumberLogPort_MarkovChainCLT_integral_pow_four_partialSum_le_of_bounded_of_exp_alpha

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FourthMomentMixingAux

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

private lemma pair_sum_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≤ j then b ^ (j.val - i.val) else 0) ≤
      (n : ℝ) * (1 - b)⁻¹ := by
  classical
  have hs : Summable (fun k : ℕ => b ^ k) := summable_geometric_of_norm_lt_one
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hb0] using hb1)
  have hrow (i : Fin n) :
      (∑ j : Fin n, if i ≤ j then b ^ (j.val - i.val) else 0) ≤ (1-b)⁻¹ := by
    calc
      (∑ j : Fin n, if i ≤ j then b ^ (j.val - i.val) else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ j), b ^ (j.val-i.val) := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ (Finset.univ.filter (fun j : Fin n => i ≤ j)).image
          (fun j => j.val-i.val), b^k := by
        rw [Finset.sum_image]
        intro a ha c hc he
        have ha' := (Finset.mem_filter.mp ha).2
        have hc' := (Finset.mem_filter.mp hc).2
        dsimp only at he
        apply Fin.ext
        omega
      _ ≤ ∑' k : ℕ, b^k := hs.sum_le_tsum _ (fun k _ => pow_nonneg hb0 k)
      _ = (1-b)⁻¹ := tsum_geometric_of_norm_lt_one
        (by simpa only [Real.norm_eq_abs, abs_of_nonneg hb0] using hb1)
  calc
    _ ≤ ∑ _i : Fin n, (1-b)⁻¹ := Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp

private lemma fourth_sum_bound {n : ℕ} (F : (Fin 4 → Fin n) → ℝ)
    (hF : ∀ v, 0 ≤ F v)
    (hperm : ∀ v (σ : Equiv.Perm (Fin 4)), F (v ∘ σ) = F v)
    (D b : ℝ) (hD : 0 ≤ D) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hord : ∀ v, Monotone v →
      F v ≤ D * b ^ ((v 1).val - (v 0).val) * b ^ ((v 3).val - (v 2).val)) :
    ∑ v, F v ≤ (24 * D * ((1-b)⁻¹)^2) * (n : ℝ)^2 := by
  classical
  let g (i j : Fin n) : ℝ := if i ≤ j then b ^ (j.val-i.val) else 0
  have hg (i j : Fin n) : 0 ≤ g i j := by dsimp [g]; split_ifs <;> positivity
  have hterm (v : Fin 4 → Fin n) :
      (if Monotone v then F v else 0) ≤ D * (g (v 0) (v 1) * g (v 2) (v 3)) := by
    split_ifs with hv
    · simpa only [g, if_pos (hv (by decide : (0 : Fin 4) ≤ 1)),
        if_pos (hv (by decide : (2 : Fin 4) ≤ 3)), mul_assoc] using hord v hv
    · exact mul_nonneg hD (mul_nonneg (hg _ _) (hg _ _))
  have hfactor : (∑ v : Fin 4 → Fin n, g (v 0) (v 1) * g (v 2) (v 3)) =
      (∑ i : Fin n, ∑ j : Fin n, g i j)^2 := by
    rw [sum_four]
    change (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
      g i j * g k l) = _
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, g i j * (∑ k : Fin n, ∑ l : Fin n, g k l) := by
        simp only [Finset.mul_sum]
      _ = (∑ i : Fin n, ∑ j : Fin n, g i j) *
          (∑ k : Fin n, ∑ l : Fin n, g k l) := by simp only [Finset.sum_mul]
      _ = _ := by rw [pow_two]
  have hG : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hg i j))
  have hGb : (∑ i : Fin n, ∑ j : Fin n, g i j) ≤ (n : ℝ)*(1-b)⁻¹ :=
    pair_sum_bound b hb0 hb1 n
  have hGsq := mul_self_le_mul_self hG hGb
  calc
    ∑ v, F v ≤ 24 * ∑ v, if Monotone v then F v else 0 :=
      sum_le_twentyfour_ordered F hF hperm
    _ ≤ 24 * ∑ v, D * (g (v 0) (v 1) * g (v 2) (v 3)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hterm v)) (by norm_num)
    _ = (24 * D) * (∑ i : Fin n, ∑ j : Fin n, g i j)^2 := by
      rw [← Finset.mul_sum, hfactor]; ring
    _ ≤ (24 * D) * ((n : ℝ)*(1-b)⁻¹)^2 :=
      mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hGsq)
        (mul_nonneg (by norm_num) hD)
    _ = _ := by ring

end FourthMomentMixingAux

namespace FourthMomentMixingAux

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
    (c a : ℝ) (ha0 : 0 ≤ a)
    (hα : ∀ n, alphaMixingCoef P X n ≤ c*a^n)
    (i j k l : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤
      (4 * (B^3)^2 * |c|) * (Real.sqrt a)^(j-i) * (Real.sqrt a)^(l-k) := by
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
  let D : ℝ := 4 * (B^3)^2 * |c|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoef (d : ℕ) : 4*(B^3)^2 * alphaMixingCoef P X d ≤ D*a^d := by
    calc
      _ ≤ 4*(B^3)^2 * (|c| *a^d) := mul_le_mul_of_nonneg_left
        ((hα d).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg ha0 d)))
        (by positivity)
      _ = _ := by dsimp [D]; ring
  have hleft : |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤ D*a^(j-i) := by
    have hcov := _root_.NumberLogPort_MarkovChainCLT_alpha_cov_bounded.solution P X hX (j-i) i (X i)
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
    exact hcov.trans (hcoef (j-i))
  have hright : |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P| ≤ D*a^(l-k) := by
    have hcov := _root_.NumberLogPort_MarkovChainCLT_alpha_cov_bounded.solution P X hX (l-k) k
      (fun ω => X i ω * X j ω * X k ω) (X l)
      (((coord_measurable X (Set.Iic k) i (by simp only [Set.mem_Iic]; omega)).mul
        (coord_measurable X (Set.Iic k) j hjk)).mul (coord_measurable X (Set.Iic k) k (by simp)))
      (coord_measurable X (Set.Ici (k+(l-k))) l (by simp only [Set.mem_Ici]; omega))
      (B^3) (by positivity) (hb3 i j k) (fun ω => (hXB l ω).trans hB3)
    rw [covariance_eq_sub (hmem3 i j k) (hmem l), hmean l, mul_zero, sub_zero] at hcov
    exact hcov.trans (hcoef (l-k))
  have hp (d : ℕ) : a^d = ((Real.sqrt a)^d)^2 := by
    conv_lhs => rw [← Real.sq_sqrt ha0]
    simp only [← pow_mul, Nat.mul_comm]
  rw [hp (j-i)] at hleft
  rw [hp (l-k)] at hright
  have hsq : |∫ ω, X i ω * X j ω * X k ω * X l ω ∂P|^2 ≤
      (D * (Real.sqrt a)^(j-i) * (Real.sqrt a)^(l-k))^2 := by
    calc
      _ ≤ (D * ((Real.sqrt a)^(j-i))^2) *
          (D * ((Real.sqrt a)^(l-k))^2) := by
        simpa only [pow_two] using mul_le_mul hleft hright (abs_nonneg _)
          (mul_nonneg hD (sq_nonneg _))
      _ = _ := by ring
  have hpos : 0 ≤ D * (Real.sqrt a)^(j-i) * (Real.sqrt a)^(l-k) := by positivity
  nlinarith

end FourthMomentMixingAux

open FourthMomentMixingAux in
-- The fourth-moment counting argument is the bounded, exponential-rate version
-- of Billingsley, Probability and Measure (3rd ed.), p. 366, equation (27.25).
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hstat : IsStrictlyStationary P X)
    (hcent : ∫ ω, X 0 ω ∂P = 0)
    (M : ℝ) (hM : ∀ i, ∀ ω, |X i ω| ≤ M)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P X n ≤ c * a ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 := by
  classical
  let B : ℝ := 1+|M|
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg M]
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hXB (i : ℕ) (ω : Ω) : |X i ω| ≤ B :=
    (hM i ω).trans (by dsimp [B]; linarith [le_abs_self M])
  let D : ℝ := 4*(B^3)^2*|c|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let b : ℝ := Real.sqrt a
  have hb0 : 0 ≤ b := Real.sqrt_nonneg a
  have hb1 : b < 1 := by dsimp [b]; nlinarith [Real.sq_sqrt ha0, Real.sqrt_nonneg a]
  refine ⟨24*D*((1-b)⁻¹)^2, by positivity, ?_⟩
  intro n
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
      F v ≤ D*b^((v 1).val-(v 0).val)*b^((v 3).val-(v 2).val) := by
    have h := ordered_product_bound P X hX (mean_coord P X hX hstat hcent)
      B hB hXB c a ha0 hα (v 0).val (v 1).val (v 2).val (v 3).val
      (hv (by decide : (0 : Fin 4) ≤ 1)) (hv (by decide : (1 : Fin 4) ≤ 2))
      (hv (by decide : (2 : Fin 4) ≤ 3))
    simpa only [F, H, Fin.prod_univ_four, D, b] using h
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
    _ ≤ _ := fourth_sum_bound F hF hperm D b hD hb0 hb1 hord

end NumberLogPort_MarkovChainCLT_integral_pow_four_partialSum_le_of_bounded_of_exp_alpha


namespace NumberLogPort_MarkovChainCLT_exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
/-
Tail-variance estimate for the MC CLT mission.
The truncation helpers through `alphaMixingCoef_nonneg` are reused from
Gabewhigham's accepted covariance proof, submission
b4ddeb01-53ae-430c-a166-0197d09d3998. The uniform-in-cutoff argument below is new.
-/

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ProbabilityTheory ENNReal Topology

namespace TailVariance

/-- Truncation of a real number at level `T`. -/
noncomputable def truncAt (T x : ℝ) : ℝ := if |x| ≤ T then x else 0

/-- The squared tail `x² 1{|x| > T}`. -/
noncomputable def tailSq (T x : ℝ) : ℝ := if |x| ≤ T then 0 else x ^ 2

theorem measurable_truncAt (T : ℝ) : Measurable (truncAt T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id
    measurable_const

theorem measurable_tailSq (T : ℝ) : Measurable (tailSq T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
    (measurable_id.pow_const 2)

theorem truncAt_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |truncAt T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simp [truncAt, hx]
  · simpa [truncAt, hx] using hT

theorem tailSq_nonneg (T x : ℝ) : 0 ≤ tailSq T x := by
  by_cases hx : |x| ≤ T <;> simp [tailSq, hx, sq_nonneg]

theorem tailSq_le_sq (T x : ℝ) : tailSq T x ≤ x ^ 2 := by
  by_cases hx : |x| ≤ T <;> simp [tailSq, hx, sq_nonneg]

/-- Pointwise control of the truncation error in a product. -/
theorem abs_mul_sub_truncAt_mul_le (T x z : ℝ) :
    |x * z - truncAt T x * truncAt T z| ≤ tailSq T x + tailSq T z := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  by_cases hx : |x| ≤ T
  · by_cases hz : |z| ≤ T
    · simp [truncAt, tailSq, hx, hz]
    · have hzT : T < |z| := lt_of_not_ge hz
      have h1 : |x * z| ≤ z ^ 2 := by
        rw [abs_mul]
        have : |x| * |z| ≤ |z| * |z| :=
          mul_le_mul_of_nonneg_right (hx.trans hzT.le) (abs_nonneg z)
        calc |x| * |z| ≤ |z| * |z| := this
          _ = z ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
      simpa [truncAt, tailSq, hx, hz] using h1.trans (by linarith)
  · have hxT : T < |x| := lt_of_not_ge hx
    by_cases hz : |z| ≤ T
    · have h1 : |x * z| ≤ x ^ 2 := by
        rw [abs_mul]
        have : |x| * |z| ≤ |x| * |x| :=
          mul_le_mul_of_nonneg_left (hz.trans hxT.le) (abs_nonneg x)
        calc |x| * |z| ≤ |x| * |x| := this
          _ = x ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
      simpa [truncAt, tailSq, hx, hz] using h1.trans (by linarith)
    · have h1 : |x * z| ≤ x ^ 2 + z ^ 2 := by
        rw [abs_mul]
        nlinarith [abs_nonneg x, abs_nonneg z, sq_nonneg (|x| - |z|), sq_abs x, sq_abs z]
      simpa [truncAt, tailSq, hx, hz] using h1

/-- Pointwise control of the truncation error in a single variable. -/
theorem mul_abs_sub_truncAt_le (T x : ℝ) :
    T * |x - truncAt T x| ≤ tailSq T x := by
  by_cases hx : |x| ≤ T
  · simp [truncAt, tailSq, hx]
  · have hxT : T < |x| := lt_of_not_ge hx
    have : T * |x| ≤ |x| * |x| := mul_le_mul_of_nonneg_right hxT.le (abs_nonneg x)
    simpa [truncAt, tailSq, hx, ← sq, sq_abs] using this

section Estimate

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The key per-lag estimate: the expectation of a product is controlled by the
mixing coefficient at the truncation level plus the squared tails. -/
theorem abs_integral_mul_le_of_cov_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (T t c : ℝ) (hT : 0 < T)
    (hX2 : MemLp X 2 P) (hZ2 : MemLp Z 2 P)
    (htX : ∫ ω, tailSq T (X ω) ∂P = t) (htZ : ∫ ω, tailSq T (Z ω) ∂P = t)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hcov : |cov[fun ω => truncAt T (X ω), fun ω => truncAt T (Z ω); P]| ≤ 4 * T ^ 2 * c) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * c + 3 * t := by
  set U : Ω → ℝ := fun ω => truncAt T (X ω) with hU
  set V : Ω → ℝ := fun ω => truncAt T (Z ω) with hV
  have hUmeas : Measurable U := (measurable_truncAt T).comp hX
  have hVmeas : Measurable V := (measurable_truncAt T).comp hZ
  have hUm : MemLp U 2 P :=
    MemLp.of_bound hUmeas.aestronglyMeasurable T
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using truncAt_bound hT.le (X ω))
  have hVm : MemLp V 2 P :=
    MemLp.of_bound hVmeas.aestronglyMeasurable T
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using truncAt_bound hT.le (Z ω))
  have hUi : Integrable U P := hUm.integrable (by norm_num)
  have hVi : Integrable V P := hVm.integrable (by norm_num)
  have hUV : Integrable (fun ω => U ω * V ω) P := hUm.integrable_mul hVm
  have hXZ : Integrable (fun ω => X ω * Z ω) P := hX2.integrable_mul hZ2
  have hZi : Integrable Z P := hZ2.integrable (by norm_num)
  have hXsq : Integrable (fun ω => X ω ^ 2) P := by
    simpa using hX2.integrable_sq
  have hZsq : Integrable (fun ω => Z ω ^ 2) P := by
    simpa using hZ2.integrable_sq
  have htailX : Integrable (fun ω => tailSq T (X ω)) P := by
    refine hXsq.mono' ((measurable_tailSq T).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  have htailZ : Integrable (fun ω => tailSq T (Z ω)) P := by
    refine hZsq.mono' ((measurable_tailSq T).comp hZ).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  -- the product error
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤ t + t := by
    rw [← integral_sub hXZ hUV]
    calc |∫ ω, (X ω * Z ω - U ω * V ω) ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (tailSq T (X ω) + tailSq T (Z ω)) ∂P :=
          integral_mono_ae (hXZ.sub hUV).abs (htailX.add htailZ)
            (ae_of_all _ fun ω => abs_mul_sub_truncAt_mul_le T (X ω) (Z ω))
      _ = t + t := by rw [integral_add htailX htailZ, htX, htZ]
  -- the mean of the truncation
  have hEV : T * |∫ ω, V ω ∂P| ≤ t := by
    have h1 : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ t := by
      rw [← integral_sub hZi hVi]
      calc T * |∫ ω, (Z ω - V ω) ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
            mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
        _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
        _ ≤ ∫ ω, tailSq T (Z ω) ∂P :=
            integral_mono_ae ((hZi.sub hVi).abs.const_mul T) htailZ
              (ae_of_all _ fun ω => mul_abs_sub_truncAt_le T (Z ω))
        _ = t := htZ
    simpa only [hZ0, zero_sub, abs_neg] using h1
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P :=
          integral_mono_ae hUi.abs (integrable_const T)
            (ae_of_all _ fun ω => truncAt_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ t := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * c + t := by
    calc |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
          congr 1
          simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * c + t := add_le_add hcov hbias
  calc |∫ ω, X ω * Z ω ∂P|
      = |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
        rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| := abs_add_le _ _
    _ ≤ (t + t) + (4 * T ^ 2 * c + t) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * c + 3 * t := by ring

end Estimate

/-- Pointwise: the number of scales `R^k` below `|x|` is controlled by `log⁺|x| / log R`. -/
theorem sum_tailSq_pow_le {R : ℝ} (hR : 1 < R) (x : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, tailSq (R ^ k) x ≤ x ^ 2 + x ^ 2 * Real.posLog |x| / Real.log R := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  set L : ℝ := Real.posLog |x| / Real.log R with hL
  have hL0 : 0 ≤ L := div_nonneg (Real.posLog_nonneg) hlogR.le
  have hsub : (Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k) ⊆
      Finset.range (⌊L⌋₊ + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, not_le] at hk
    obtain ⟨-, hk2⟩ := hk
    have hxpos : (0 : ℝ) < |x| := lt_of_le_of_lt (by positivity) hk2
    have hlog : (k : ℝ) * Real.log R < Real.log |x| := by
      have := Real.log_lt_log (by positivity) hk2
      rwa [Real.log_pow] at this
    have hle : Real.log |x| ≤ Real.posLog |x| := by
      rw [Real.posLog_def]; exact le_max_right _ _
    have : (k : ℝ) < L := by
      rw [hL, lt_div_iff₀ hlogR]
      linarith
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor this.le))
  have hcard : (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) ≤ L + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have : (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) ≤ (⌊L⌋₊ + 1 : ℕ) := by
      exact_mod_cast h1
    refine this.trans ?_
    push_cast
    have := Nat.floor_le hL0
    linarith
  have hsum : ∑ k ∈ Finset.range N, tailSq (R ^ k) x
      = x ^ 2 * (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) := by
    simp only [tailSq]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_zero, zero_add, nsmul_eq_mul,
      mul_comm]
  rw [hsum]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc x ^ 2 * (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ)
      ≤ x ^ 2 * (L + 1) := mul_le_mul_of_nonneg_left hcard hx2
    _ = x ^ 2 + x ^ 2 * Real.posLog |x| / Real.log R := by rw [hL]; ring

section LogMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An `x² log⁺|x|` moment forces square integrability. -/
theorem memLp_two_of_logMoment (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hmom : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) P) :
    MemLp X 2 P := by
  refine (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).2 ?_
  refine ((integrable_const (Real.exp 2)).add hmom).mono'
    (hX.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hpos : 0 ≤ X ω ^ 2 * Real.posLog |X ω| :=
    mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hexp : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  by_cases hx : |X ω| ≤ Real.exp 1
  · have : X ω ^ 2 ≤ Real.exp 2 := by
      have h1 : |X ω| ^ 2 ≤ Real.exp 1 ^ 2 := by
        have := mul_self_le_mul_self (abs_nonneg (X ω)) hx
        nlinarith
      calc X ω ^ 2 = |X ω| ^ 2 := (sq_abs _).symm
        _ ≤ Real.exp 1 ^ 2 := h1
        _ = Real.exp 2 := hexp
    simp only [Pi.add_apply]
    linarith
  · have hxe : Real.exp 1 < |X ω| := lt_of_not_ge hx
    have h1 : (1 : ℝ) ≤ Real.posLog |X ω| := by
      have hge : (1 : ℝ) ≤ Real.log |X ω| := by
        have h := Real.log_lt_log (Real.exp_pos 1) hxe
        rw [Real.log_exp] at h
        exact h.le
      rw [Real.posLog_def]
      exact le_max_of_le_right hge
    have h2 : X ω ^ 2 ≤ X ω ^ 2 * Real.posLog |X ω| := by
      nlinarith [sq_nonneg (X ω)]
    simp only [Pi.add_apply]
    have : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos 2).le
    linarith

/-- The squared tails at the geometric scales `R^k` are summable. -/
theorem summable_integral_tailSq (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hmom : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) P)
    {R : ℝ} (hR : 1 < R) :
    Summable (fun k : ℕ => ∫ ω, tailSq (R ^ k) (X ω) ∂P) := by
  have hX2 : MemLp X 2 P := memLp_two_of_logMoment P X hX hmom
  have hXsq : Integrable (fun ω => X ω ^ 2) P := hX2.integrable_sq
  have hint : ∀ k : ℕ, Integrable (fun ω => tailSq (R ^ k) (X ω)) P := by
    intro k
    refine hXsq.mono' ((measurable_tailSq _).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  refine summable_of_sum_range_le
    (fun k => integral_nonneg fun ω => tailSq_nonneg _ _)
    (c := (∫ ω, X ω ^ 2 ∂P) + (∫ ω, X ω ^ 2 * Real.posLog |X ω| ∂P) / Real.log R) ?_
  intro N
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, tailSq (R ^ k) (X ω)) P :=
    integrable_finsetSum _ fun k _ => hint k
  calc ∑ k ∈ Finset.range N, ∫ ω, tailSq (R ^ k) (X ω) ∂P
      = ∫ ω, ∑ k ∈ Finset.range N, tailSq (R ^ k) (X ω) ∂P :=
        (integral_finsetSum _ fun k _ => hint k).symm
    _ ≤ ∫ ω, (X ω ^ 2 + X ω ^ 2 * Real.posLog |X ω| / Real.log R) ∂P :=
        integral_mono hsumint (hXsq.add (hmom.div_const _))
          (fun ω => sum_tailSq_pow_le hR (X ω) N)
    _ = (∫ ω, X ω ^ 2 ∂P) + (∫ ω, X ω ^ 2 * Real.posLog |X ω| ∂P) / Real.log R := by
        rw [integral_add hXsq (hmom.div_const _), integral_div]

end LogMoment

section Main

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under strict stationarity every coordinate has the law of the first one. -/
theorem identDistrib_coord (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hshift : Measurable (fun ω n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hfull : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) hshift,
    Measure.map_map (measurable_pi_apply 0) hfull] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

omit [MeasurableSpace Ω] in
/-- A coordinate is measurable for the process σ-algebra of any index set containing it. -/
theorem measurable_coord {E : Type*} [MeasurableSpace E] (Y : ℕ → Ω → E) (s : Set ℕ)
    (i : ℕ) (hi : i ∈ s) : Measurable[processSigma Y s] (Y i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

/-- The strong mixing coefficient is nonnegative. -/
theorem alphaMixingCoef_nonneg {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _



/-- Variance expansion adapted from WillR's accepted submission
22190ef3-0b53-4770-9441-4c54c00d05a1. Absolute covariance summability
bounds every partial sum, rather than only its asymptotic variance. -/
theorem partialSum_sq_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) ≤
      ((∫ ω, Y 0 ω ^ 2 ∂P) + 2 * ∑' k, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) * n := by
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

  have hsm : ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmemLp i).integrable (by norm_num))]
    simp [hmean]
  have hvm : Var[∑ i ∈ Finset.range n, Y i; P] =
      ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P := by
    rw [variance_eq_integral (memLp_finsetSum' _ (fun i _ => hmemLp i)).aemeasurable]
    simp only [Finset.sum_apply, hsm, sub_zero]
  have hc0 : c 0 = ∫ ω, Y 0 ω ^ 2 ∂P := by simp only [hc, pow_two]
  have hbound : ∀ m : ℕ, ∑ k ∈ Finset.range m, c (k + 1) ≤ ∑' k, |c (k + 1)| := by
    intro m
    exact (Finset.sum_le_sum (fun k _ => le_abs_self _)).trans
      (hsum.sum_le_tsum (Finset.range m) (fun k _ => abs_nonneg _))
  rw [← hvm, hVD n]
  calc (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1)
      ≤ (n : ℝ) * c 0 + 2 * ∑ _m ∈ Finset.range n, ∑' k, |c (k + 1)| := by
        gcongr with m hm
        exact hbound m
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc, pow_two]; ring

/-- A product's first absolute moment is bounded by the common second moment. -/
theorem abs_integral_mul_le_second
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

noncomputable def high (T x : ℝ) : ℝ := if T < |x| then x else 0

lemma measurable_high (T : ℝ) : Measurable (high T) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_id measurable_const

lemma high_abs_le (T x : ℝ) : |high T x| ≤ |x| := by
  unfold high
  split_ifs <;> simp [abs_nonneg]

lemma high_sq (T x : ℝ) : high T x ^ 2 = tailSq T x := by
  by_cases h : T < |x|
  · simp [high, tailSq, h, not_le.mpr h]
  · simp [high, tailSq, h, le_of_not_gt h]

lemma tailSq_mono_abs {S x w : ℝ} (h : |x| ≤ |w|) : tailSq S x ≤ tailSq S w := by
  by_cases hx : |x| ≤ S
  · simpa [tailSq, hx] using tailSq_nonneg S w
  · have hw : ¬ |w| ≤ S := fun hw => hx (h.trans hw)
    simp only [tailSq, hx, hw, if_false]
    nlinarith [sq_abs x, sq_abs w, abs_nonneg x, abs_nonneg w]

lemma memLp_high (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 P) (T : ℝ) : MemLp (fun ω => high T (X ω)) 2 P := by
  exact hX2.mono ((measurable_high T).comp hX).aestronglyMeasurable
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
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), high_sq]
  exact tailSq_le_sq _ _

/-- A common log-moment envelope gives one summable covariance bound for
an entire family of centered exponentially mixing processes. -/
theorem exists_uniform_covariance_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N i, Measurable (Z N i))
    (hstat : ∀ N, IsStrictlyStationary P (Z N))
    (hcent : ∀ N, ∫ ω, Z N 0 ω ∂P = 0)
    (hL2 : ∀ N, MemLp (Z N 0) 2 P)
    (W : Ω → ℝ) (hW : Measurable W)
    (hmom : Integrable (fun ω => W ω ^ 2 * Real.posLog |W ω|) P)
    (henv : ∀ N ω, |Z N 0 ω| ≤ |W ω|)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hal : ∀ N n, alphaMixingCoef P (Z N) n ≤ c * a ^ n) :
    ∃ B : ℕ → ℝ, Summable B ∧ (∀ k, 0 ≤ B k) ∧
      ∀ N k, |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P| ≤ B k := by
  have hc0 : 0 ≤ c := by
    have hh := (alphaMixingCoef_nonneg P (Z 0) 0).trans (hal 0 0)
    simpa using hh
  have h1a : (0 : ℝ) < 1 + a := by linarith
  let R : ℝ := Real.sqrt (2 / (1 + a))
  have hR2 : R ^ 2 = 2 / (1 + a) := Real.sq_sqrt (by positivity)
  have hR1 : 1 < R := by
    have hh : (1 : ℝ) < 2 / (1 + a) := by rw [lt_div_iff₀ h1a]; linarith
    nlinarith [Real.sqrt_nonneg (2 / (1 + a)), hR2]
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  let q : ℝ := a * R ^ 2
  have hq0 : 0 ≤ q := mul_nonneg ha0 (sq_nonneg R)
  have hq1 : q < 1 := by
    dsimp [q]
    rw [hR2, mul_div_assoc', div_lt_one h1a]
    linarith
  let t : ℕ → ℝ := fun k => ∫ ω, tailSq (R ^ k) (W ω) ∂P
  have htail : Summable t := summable_integral_tailSq P W hW hmom hR1
  let B : ℕ → ℝ := fun k => 4 * c * a * q ^ k + 3 * t k
  have hB : Summable B :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (4 * c * a)).add (htail.mul_left 3)
  have ht0 : ∀ k, 0 ≤ t k := fun k => integral_nonneg fun ω => tailSq_nonneg _ _
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    have ht := ht0 k
    dsimp [B]
    positivity
  refine ⟨B, hB, hB0, ?_⟩
  intro N k
  have hid := identDistrib_coord P (Z N) (hZ N) (hstat N) (k + 1)
  have hZ2 : MemLp (Z N (k + 1)) 2 P := hid.memLp_iff.mpr (hL2 N)
  have hZ0 : ∫ ω, Z N (k + 1) ω ∂P = 0 := hid.integral_eq.trans (hcent N)
  let tN : ℝ := ∫ ω, tailSq (R ^ k) (Z N 0 ω) ∂P
  have htZ : ∫ ω, tailSq (R ^ k) (Z N (k + 1) ω) ∂P = tN :=
    (hid.comp (measurable_tailSq (R ^ k))).integral_eq
  have hTpos : (0 : ℝ) < R ^ k := by positivity
  have hcov : |cov[fun ω => truncAt (R ^ k) (Z N 0 ω),
      fun ω => truncAt (R ^ k) (Z N (k + 1) ω); P]|
      ≤ 4 * (R ^ k) ^ 2 * alphaMixingCoef P (Z N) (k + 1) := by
    exact _root_.NumberLogPort_MarkovChainCLT_alpha_cov_bounded.solution P (Z N) (hZ N) (k + 1) 0 _ _
      ((measurable_truncAt _).comp (measurable_coord (Z N) (Set.Iic 0) 0 (by simp)))
      ((measurable_truncAt _).comp
        (measurable_coord (Z N) (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
      (R ^ k) hTpos.le (fun ω => truncAt_bound hTpos.le _)
      (fun ω => truncAt_bound hTpos.le _)
  have hfirst := abs_integral_mul_le_of_cov_bound P (Z N 0) (Z N (k + 1))
    (hZ N 0) (hZ N (k + 1)) (R ^ k) tN (alphaMixingCoef P (Z N) (k + 1))
    hTpos (hL2 N) hZ2 rfl htZ hZ0 hcov
  have hW2 := memLp_two_of_logMoment P W hW hmom
  have htailInt : ∀ (X : Ω → ℝ), Measurable X → MemLp X 2 P →
      Integrable (fun ω => tailSq (R ^ k) (X ω)) P := by
    intro X hX hX2
    exact hX2.integrable_sq.mono' ((measurable_tailSq _).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
        exact tailSq_le_sq _ _)
  have htN : tN ≤ t k :=
    integral_mono (htailInt _ (hZ N 0) (hL2 N)) (htailInt W hW hW2)
      (fun ω => tailSq_mono_abs (henv N ω))
  calc |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
      ≤ 4 * (R ^ k) ^ 2 * alphaMixingCoef P (Z N) (k + 1) + 3 * tN := hfirst
    _ ≤ 4 * (R ^ k) ^ 2 * (c * a ^ (k + 1)) + 3 * t k := by
      gcongr
      exact hal N (k + 1)
    _ = B k := by
      dsimp [B, q]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring_nf

end Main
end TailVariance

open TailVariance

/-- The centered high part contributes arbitrarily little variance per sample. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n,
        ((if T < |Y i ω| then Y i ω else 0)
          - ∫ ω', (if T < |Y 0 ω'| then Y 0 ω' else 0) ∂P)) ^ 2 ∂P ≤ ε * n := by
  have hY02 : MemLp (Y 0) 2 P := memLp_two_of_logMoment P (Y 0) (hY 0) hmom
  have hYi2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    (identDistrib_coord P Y hY hstat i).memLp_iff.mpr hY02
  let m : ℕ → ℝ := fun N => ∫ ω, high (N : ℝ) (Y 0 ω) ∂P
  let g : ℕ → ℝ → ℝ := fun N x => high (N : ℝ) x - m N
  let Z : ℕ → ℕ → Ω → ℝ := fun N i ω => g N (Y i ω)
  have hg : ∀ N, Measurable (g N) := fun N => (measurable_high (N : ℝ)).sub_const (m N)
  have hZ : ∀ N i, Measurable (Z N i) := fun N i => (hg N).comp (hY i)
  have hHs : ∀ (N i : ℕ), MemLp (fun ω => high (N : ℝ) (Y i ω)) 2 P :=
    fun N i => memLp_high P (Y i) (hY i) (hYi2 i) (N : ℝ)
  have hZ2 : ∀ N i, MemLp (Z N i) 2 P := fun N i => (hHs N i).sub (memLp_const (m N))
  have hZstat : ∀ N, IsStrictlyStationary P (Z N) := fun N =>
    isStrictlyStationary_comp_of_measurable P Y hY hstat (g N) (hg N)
  have hZcent : ∀ N, ∫ ω, Z N 0 ω ∂P = 0 := by
    intro N
    dsimp [Z, g]
    rw [integral_sub ((hHs N 0).integrable (by norm_num)) (integrable_const (m N))]
    simp [m]
  have hZα : ∀ N k, alphaMixingCoef P (Z N) k ≤ c * a ^ k := by
    intro N k
    exact (alphaMixingCoef_comp_nonneg_le_of_finite P Y (g N) (hg N) k).2.trans (hα k)
  let C : ℝ := ∫ ω, |Y 0 ω| ∂P
  have hC0 : 0 ≤ C := integral_nonneg fun ω => abs_nonneg _
  have hm : ∀ N, |m N| ≤ C := by
    intro N
    exact abs_integral_le_integral_abs.trans
      (integral_mono ((hHs N 0).integrable (by norm_num)).abs
        (hY02.integrable (by norm_num)).abs (fun ω => high_abs_le (N : ℝ) (Y 0 ω)))
  let W : Ω → ℝ := fun ω => |Y 0 ω| + C
  have hW : Measurable W := (hY 0).abs.add_const C
  have hWmom : Integrable (fun ω => W ω ^ 2 * Real.posLog |W ω|) P := by
    have habsmom : Integrable (fun ω => |Y 0 ω| ^ 2 * Real.posLog |(|Y 0 ω|)|) P := by
      simpa only [sq_abs, abs_abs] using hmom
    have hh := (memLp_two_and_logMoment_sub_const P (fun ω => |Y 0 ω|)
      (hY 0).abs habsmom (-C)).2
    simpa only [sub_neg_eq_add] using hh
  have henv : ∀ N ω, |Z N 0 ω| ≤ |W ω| := by
    intro N ω
    have hw : 0 ≤ W ω := add_nonneg (abs_nonneg _) hC0
    rw [abs_of_nonneg hw]
    calc |Z N 0 ω| ≤ |high (N : ℝ) (Y 0 ω)| + |m N| := by
          simpa only [Z, g, sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (high (N : ℝ) (Y 0 ω)) 0 (m N))
      _ ≤ W ω := add_le_add (high_abs_le (N : ℝ) (Y 0 ω)) (hm N)
  obtain ⟨B, hB, hB0, hbound⟩ := exists_uniform_covariance_bound P Z hZ hZstat hZcent
    (fun N => hZ2 N 0) W hW hWmom henv c a ha0 ha1 hZα
  let v : ℕ → ℝ := fun N => ∫ ω, Z N 0 ω ^ 2 ∂P
  have hv0 : ∀ N, 0 ≤ v N := fun N => integral_nonneg fun ω => sq_nonneg _
  have hvle : ∀ N, v N ≤ ∫ ω, high (N : ℝ) (Y 0 ω) ^ 2 ∂P := by
    intro N
    change (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) ≤ _
    rw [show (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) =
      Var[fun ω => high (N : ℝ) (Y 0 ω); P] from
        (variance_eq_integral ((measurable_high (N : ℝ)).comp (hY 0)).aemeasurable).symm]
    exact variance_le_expectation_sq ((measurable_high (N : ℝ)).comp (hY 0)).aestronglyMeasurable
  have hvlim : Tendsto v atTop (𝓝 0) :=
    squeeze_zero hv0 hvle (tendsto_integral_high_sq P (Y 0) (hY 0) hY02)
  let r : ℕ → ℕ → ℝ := fun N k => |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
  have hrle : ∀ N k, r N k ≤ v N := by
    intro N k
    apply abs_integral_mul_le_second P _ _ (hZ2 N 0) (hZ2 N (k + 1))
    exact ((identDistrib_coord P (Z N) (hZ N) (hZstat N) (k + 1)).comp
      (measurable_id.pow_const 2)).integral_eq
  have hrlim : ∀ k, Tendsto (fun N => r N k) atTop (𝓝 0) := fun k =>
    squeeze_zero (fun N => abs_nonneg _) (fun N => hrle N k) hvlim
  have hrlim_sum : Tendsto (fun N => ∑' k, r N k) atTop (𝓝 0) := by
    have hh := tendsto_tsum_of_dominated_convergence hB hrlim
      (Filter.Eventually.of_forall (fun N k => ?_))
    · simpa using hh
    simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k
  have hrsum : ∀ N, Summable (r N) := fun N =>
    hB.of_norm_bounded (fun k => by simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k)
  have htot : Tendsto (fun N => v N + 2 * ∑' k, r N k) atTop (𝓝 0) := by
    simpa using hvlim.add (hrlim_sum.const_mul 2)
  have hevent : ∀ᶠ N in atTop, v N + 2 * ∑' k, r N k < ε :=
    htot.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN, hsmall⟩ := (eventually_ge_atTop 1 |>.and hevent).exists
  refine ⟨(N : ℝ), by exact_mod_cast (show 0 < N by omega), ?_⟩
  intro n
  have hh := partialSum_sq_le P (Z N) (hZ N) (hZstat N) (hZcent N) (hZ2 N 0) (hrsum N) n
  have hlast : (v N + 2 * ∑' k, r N k) * (n : ℝ) ≤ ε * n :=
    mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg n)
  exact hh.trans hlast

end NumberLogPort_MarkovChainCLT_exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment


namespace NumberLogPort_MarkovChainCLT_summable_covariance_of_exp_alpha_of_log_moment

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

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LogCovariance

noncomputable def trunc (T x : ℝ) : ℝ := if |x| ≤ T then x else 0
noncomputable def tail (T x : ℝ) : ℝ := if T < |x| then x ^ 2 else 0

theorem measurable_trunc (T : ℝ) : Measurable (trunc T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

theorem measurable_tail (T : ℝ) : Measurable (tail T) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) (measurable_id.pow_const 2) measurable_const

theorem trunc_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |trunc T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simpa [trunc, hx] using hx
  · simpa [trunc, hx] using hT

theorem tail_nonneg (T x : ℝ) : 0 ≤ tail T x := by
  unfold tail
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem tail_le_sq (T x : ℝ) : tail T x ≤ x ^ 2 := by
  unfold tail
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

theorem product_tail (T x y : ℝ) :
    |x * y - trunc T x * trunc T y| ≤ tail T x + tail T y := by
  by_cases hx : |x| ≤ T
  · by_cases hy : |y| ≤ T
    · simp [trunc, tail, hx, hy, not_lt.mpr hx, not_lt.mpr hy]
    · have hy' : T < |y| := lt_of_not_ge hy
      have hprod := mul_le_mul_of_nonneg_right (hx.trans hy'.le) (abs_nonneg y)
      simp only [trunc, hx, hy, if_true, if_false, mul_zero, sub_zero, tail,
        not_lt.mpr hx, hy', zero_add, abs_mul]
      nlinarith [sq_abs y]
  · have hx' : T < |x| := lt_of_not_ge hx
    by_cases hy : |y| ≤ T
    · have hprod := mul_le_mul_of_nonneg_left (hy.trans hx'.le) (abs_nonneg x)
      simp only [trunc, hx, hy, if_true, if_false, zero_mul, sub_zero, tail,
        not_lt.mpr hy, hx', add_zero, abs_mul]
      nlinarith [sq_abs x]
    · have hy' : T < |y| := lt_of_not_ge hy
      simp only [trunc, hx, hy, if_false, zero_mul, sub_zero, tail, hx', hy', if_true, abs_mul]
      nlinarith [sq_abs x, sq_abs y, sq_nonneg (|x| - |y|)]

theorem single_tail (T y : ℝ) :
    T * |y - trunc T y| ≤ tail T y := by
  by_cases hy : |y| ≤ T
  · simp [trunc, tail, hy, not_lt.mpr hy]
  · have hy' : T < |y| := lt_of_not_ge hy
    have hprod := mul_le_mul_of_nonneg_right hy'.le (abs_nonneg y)
    simp only [trunc, hy, if_false, sub_zero, tail, hy', if_true]
    nlinarith [sq_abs y]

theorem tail_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (hX2 : MemLp X 2 P) (T : ℝ) :
    Integrable (fun ω => tail T (X ω)) P := by
  refine hX2.integrable_sq.mono' ((measurable_tail T).comp hX).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (tail_nonneg T (X ω))] using tail_le_sq T (X ω)

end LogCovariance

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LogCovariance

theorem truncation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hX2 : MemLp X 2 P) (hZ2 : MemLp Z 2 P)
    (T M a : ℝ) (hT : 0 < T)
    (hXM : ∫ ω, tail T (X ω) ∂P = M) (hZM : ∫ ω, tail T (Z ω) ∂P = M)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hc : |cov[fun ω => trunc T (X ω), fun ω => trunc T (Z ω); P]| ≤ 4 * T ^ 2 * a) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * a + 3 * M := by
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
  have hXZ : Integrable (fun ω => X ω * Z ω) P := hX2.integrable_mul hZ2
  have hZi : Integrable Z P := hZ2.integrable (by norm_num)
  have hXt := tail_integrable P X hX hX2 T
  have hZt := tail_integrable P Z hZ hZ2 T
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤ M + M := by
    rw [← integral_sub hXZ hUV]
    calc
      |∫ ω, X ω * Z ω - U ω * V ω ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, tail T (X ω) + tail T (Z ω) ∂P :=
        integral_mono_ae (hXZ.sub hUV).abs (hXt.add hZt)
          (ae_of_all _ fun ω => product_tail T (X ω) (Z ω))
      _ = M + M := by rw [integral_add hXt hZt, hXM, hZM]
  have hsingle : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ M := by
    rw [← integral_sub hZi hVi]
    calc
      T * |∫ ω, Z ω - V ω ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
      _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
      _ ≤ ∫ ω, tail T (Z ω) ∂P :=
        integral_mono_ae ((hZi.sub hVi).abs.const_mul T) hZt
          (ae_of_all _ fun ω => single_tail T (Z ω))
      _ = M := hZM
  have hEV : T * |∫ ω, V ω ∂P| ≤ M := by
    simpa only [hZ0, zero_sub, abs_neg] using hsingle
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc
      |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P := integral_mono_ae hUi.abs (integrable_const T)
        (ae_of_all _ fun ω => trunc_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * a + M := by
    calc
      |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
        congr 1
        simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * a + M := add_le_add hc hbias
  calc
    |∫ ω, X ω * Z ω ∂P| =
        |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
      rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| :=
      abs_add_le _ _
    _ ≤ (M + M) + (4 * T ^ 2 * a + M) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * a + 3 * M := by ring

end LogCovariance

namespace LogGeometric

theorem exists_rate (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ r : ℝ, 0 < r ∧ Summable (fun n : ℕ => Real.exp (r * (n : ℝ)) ^ 2 * a ^ n) := by
  let b : ℝ := (a + 1) / 2
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hab : a < b := by dsimp [b]; linarith
  let r : ℝ := -Real.log b / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [Real.log_neg hb0 hb1]
  have hexp : Real.exp (2 * r) = b⁻¹ := by
    rw [show 2 * r = -Real.log b by dsimp [r]; ring, Real.exp_neg, Real.exp_log hb0]
  have hq0 : 0 ≤ Real.exp (2 * r) * a := mul_nonneg (Real.exp_pos _).le ha0
  have hq1 : Real.exp (2 * r) * a < 1 := by
    rw [hexp, ← div_eq_inv_mul]
    exact (div_lt_one hb0).mpr hab
  refine ⟨r, hr, ?_⟩
  have hs : Summable (fun n : ℕ => (Real.exp (2 * r) * a) ^ n) := summable_geometric_of_norm_lt_one (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  convert hs using 1
  funext n
  rw [mul_pow]
  congr 1
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end LogGeometric

open MeasureTheory
open scoped BigOperators

namespace LogTailSeries

theorem sum_exp_square_tails_le (x r : ℝ) (hr : 0 < r) (N : ℕ) :
    (∑ n ∈ Finset.range N, if Real.exp (r * (n : ℝ)) < |x| then x ^ 2 else 0) ≤
      x ^ 2 * (1 + Real.posLog |x| / r) := by
  classical
  let q := Real.posLog |x| / r
  have hq : 0 ≤ q := div_nonneg Real.posLog_nonneg hr.le
  have hsub : (Finset.range N).filter (fun n : ℕ => Real.exp (r * (n : ℝ)) < |x|) ⊆
      Finset.range (Nat.ceil q) := by
    intro n hn
    obtain ⟨_, hn⟩ := Finset.mem_filter.mp hn
    have hlog : r * (n : ℝ) < Real.log |x| := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hn
    have hposlog : Real.log |x| ≤ Real.posLog |x| := le_max_right _ _
    apply Finset.mem_range.mpr
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hr).mpr
    simpa only [mul_comm] using hlog.trans_le hposlog
  calc
    (∑ n ∈ Finset.range N, if Real.exp (r * (n : ℝ)) < |x| then x ^ 2 else 0) =
        ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Real.exp (r * (n : ℝ)) < |x|), x ^ 2 :=
      (Finset.sum_filter _ _).symm
    _ ≤ ∑ _n ∈ Finset.range (Nat.ceil q), x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg x)
    _ = (Nat.ceil q : ℝ) * x ^ 2 := by simp
    _ ≤ (q + 1) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hq).le (sq_nonneg x)
    _ = x ^ 2 * (1 + Real.posLog |x| / r) := by dsimp [q]; ring

theorem summable_exp_square_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (h2 : Integrable (fun ω => X ω ^ 2) μ)
    (hlog : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) μ)
    (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℕ =>
      ∫ ω, if Real.exp (r * (n : ℝ)) < |X ω| then X ω ^ 2 else 0 ∂μ) := by
  classical
  let F : ℕ → Ω → ℝ :=
    fun n ω => if Real.exp (r * (n : ℝ)) < |X ω| then X ω ^ 2 else 0
  have hFi (n : ℕ) : Integrable (F n) μ :=
    h2.indicator (measurableSet_lt measurable_const hX.abs)
  have hF0 (n : ℕ) (ω : Ω) : 0 ≤ F n ω := by
    dsimp [F]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have henv : Integrable (fun ω => X ω ^ 2 * (1 + Real.posLog |X ω| / r)) μ := by
    convert h2.add (hlog.div_const r) using 1 <;>
      first | rfl | (funext ω; simp only [Pi.add_apply, Pi.div_apply]; ring)
  apply summable_of_sum_range_le (fun n => integral_nonneg (hF0 n))
  intro N
  calc
    (∑ n ∈ Finset.range N, ∫ ω, F n ω ∂μ) = ∫ ω, ∑ n ∈ Finset.range N, F n ω ∂μ :=
      (integral_finsetSum (Finset.range N) (fun n _ => hFi n)).symm
    _ ≤ ∫ ω, X ω ^ 2 * (1 + Real.posLog |X ω| / r) ∂μ :=
      integral_mono_ae (integrable_finsetSum _ (fun n _ => hFi n)) henv
        (ae_of_all μ fun ω => sum_exp_square_tails_le (X ω) r hr N)

end LogTailSeries

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  obtain ⟨r, hr, hgeom⟩ := LogGeometric.exists_rate a ha0 ha1
  have h02 : MemLp (Y 0) 2 P := (memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  have ht := LogTailSeries.summable_exp_square_tails P (Y 0) (hY 0) h02.integrable_sq hmom r hr
  have hg : Summable (fun n : ℕ => 4 * Real.exp (r * (n : ℝ)) ^ 2 * (max c 0 * a ^ n)) := by
    convert hgeom.mul_left (4 * max c 0) using 1 <;> first | rfl | (funext n; ring)
  have hs : Summable (fun n : ℕ =>
      4 * Real.exp (r * (n : ℝ)) ^ 2 * (max c 0 * a ^ n) +
        3 * ∫ ω, LogCovariance.tail (Real.exp (r * (n : ℝ))) (Y 0 ω) ∂P) :=
    hg.add (ht.mul_left 3)
  apply ((summable_nat_add_iff 1).mpr hs).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs]
  let T := Real.exp (r * ((k + 1 : ℕ) : ℝ))
  let M := ∫ ω, LogCovariance.tail T (Y 0 ω) ∂P
  have hT : 0 < T := Real.exp_pos _
  have hid := CovarianceStationarity.identDistrib_coord P Y hY hstat (k + 1)
  have hk2 : MemLp (Y (k + 1)) 2 P := hid.memLp_iff.mpr h02
  have hkM : ∫ ω, LogCovariance.tail T (Y (k + 1) ω) ∂P = M :=
    (hid.comp (LogCovariance.measurable_tail T)).integral_eq
  have hk0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  have hc := _root_.NumberLogPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY (k + 1) 0
    (fun ω => LogCovariance.trunc T (Y 0 ω))
    (fun ω => LogCovariance.trunc T (Y (k + 1) ω))
    ((LogCovariance.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Iic 0) 0 (by simp)))
    ((LogCovariance.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
    T hT.le (fun ω => LogCovariance.trunc_bound hT.le (Y 0 ω))
    (fun ω => LogCovariance.trunc_bound hT.le (Y (k + 1) ω))
  have hbound := LogCovariance.truncation_estimate P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    h02 hk2 T M (alphaMixingCoef P Y (k + 1)) hT rfl hkM hk0 hc
  refine hbound.trans ?_
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (hα (k + 1)).trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg ha0 _))




end NumberLogPort_MarkovChainCLT_summable_covariance_of_exp_alpha_of_log_moment


namespace NumberLogPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum

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

end NumberLogPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum


namespace NumberLogPort_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (d : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hX : ∀ n, Measurable (X n))
    (hd : Tendsto (fun n : ℕ => d n / Real.sqrt n) atTop (𝓝 s))
    (hnorm : TendstoInDistribution (fun (n : ℕ) ω => X n ω / d n) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * X n ω) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (s ^ 2))) := by
  have hXmeas : ∀ n : ℕ, Measurable (fun ω => (Real.sqrt n)⁻¹ * X n ω) :=
    fun n => by fun_prop
  have hYmeas : ∀ n, Measurable (fun _ : Ω => d n / Real.sqrt n) :=
    fun n => by fun_prop
  have hYlim : TendstoInMeasure P (fun n _ => d n / Real.sqrt n) atTop (fun _ => s) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
    exact Filter.Eventually.of_forall fun _ => hd
  have hSlutsky : TendstoInDistribution (fun n ω => X n ω / d n * (d n / Real.sqrt n)) atTop
      (fun ω => id ω * s) (fun _ => P) (gaussianReal 0 1) :=
    hnorm.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 * p.2) continuous_mul hYlim
      (fun n => (hYmeas n).aemeasurable)
  have hmap : (gaussianReal 0 1).map (fun ω : ℝ => id ω * s)
      = gaussianReal 0 (Real.toNNReal (s ^ 2)) := by
    have e : (fun ω : ℝ => id ω * s) = (s * ·) := by
      funext ω; simp [mul_comm]
    rw [e, gaussianReal_map_const_mul, mul_zero]
    congr 1
    rw [mul_one]
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (sq_nonneg s)).symm
  have hev : ∀ᶠ n in atTop, d n ≠ 0 ∧ 1 ≤ n := by
    have hpos : ∀ᶠ n in atTop, d n / Real.sqrt n ∈ Set.Ioi 0 :=
      hd.eventually (Ioi_mem_nhds hs)
    filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    refine ⟨?_, hn1⟩
    intro h0
    rw [h0, zero_div] at hn
    simp at hn
  have hlim_meas : AEMeasurable (id : ℝ → ℝ) (gaussianReal 0 (Real.toNNReal (s ^ 2))) :=
    measurable_id.aemeasurable
  have hPtval : (gaussianReal 0 1).map (fun ω : ℝ => id ω * s)
      = (gaussianReal 0 (Real.toNNReal (s ^ 2))).map id := by
    rw [hmap, Measure.map_id]
  have hPt : (⟨(gaussianReal 0 1).map (fun ω : ℝ => id ω * s),
      Measure.isProbabilityMeasure_map hSlutsky.aemeasurable_limit⟩ : ProbabilityMeasure ℝ)
      = ⟨(gaussianReal 0 (Real.toNNReal (s ^ 2))).map id,
      Measure.isProbabilityMeasure_map hlim_meas⟩ :=
    Subtype.ext hPtval
  have hStep1 := hPt ▸ hSlutsky.tendsto
  have hmaps : ∀ᶠ n in atTop, (⟨P.map (fun ω => X n ω / d n * (d n / Real.sqrt n)),
        Measure.isProbabilityMeasure_map (hSlutsky.forall_aemeasurable n)⟩ : ProbabilityMeasure ℝ)
      = ⟨P.map (fun ω => (Real.sqrt n)⁻¹ * X n ω),
        Measure.isProbabilityMeasure_map (hXmeas n).aemeasurable⟩ := by
    filter_upwards [hev] with n ⟨hdn, hn1⟩
    have hfun : (fun ω => X n ω / d n * (d n / Real.sqrt n))
        = (fun ω => (Real.sqrt n)⁻¹ * X n ω) := by
      funext ω
      rw [div_mul_div_comm, mul_comm (d n) (Real.sqrt n),
        mul_div_mul_right _ _ hdn, div_eq_inv_mul]
    exact Subtype.ext (show P.map (fun ω => X n ω / d n * (d n / Real.sqrt n))
      = P.map (fun ω => (Real.sqrt n)⁻¹ * X n ω) from by rw [hfun])
  have hfin := hStep1.congr' hmaps
  exact ⟨fun n => (hXmeas n).aemeasurable, measurable_id.aemeasurable, hfin⟩

end NumberLogPort_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized


namespace NumberLogPort_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

private noncomputable def truncLow (T x : ℝ) : ℝ := if T < |x| then 0 else x

private noncomputable def truncHigh (T x : ℝ) : ℝ := if T < |x| then x else 0

private theorem truncLow_add_truncHigh (T x : ℝ) : truncLow T x + truncHigh T x = x := by
  unfold truncLow truncHigh
  split_ifs <;> ring

private theorem measurable_truncLow (T : ℝ) : Measurable (truncLow T) := by
  unfold truncLow
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
    measurable_id

private theorem measurable_truncHigh (T : ℝ) : Measurable (truncHigh T) := by
  unfold truncHigh
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_id
    measurable_const

private theorem abs_truncLow_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |truncLow T x| ≤ T := by
  unfold truncLow
  split_ifs with h
  · simpa using hT
  · exact le_of_not_gt h

private theorem memLp_two_of_stationary (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P)
    (i : ℕ) : MemLp (Y i) 2 P := by
  have hmi : Measurable (fun ω => (fun n => Y (n + i) ω)) :=
    measurable_pi_lambda _ fun n => hY (n + i)
  have hm0 : Measurable (fun ω => (fun n => Y n ω)) :=
    measurable_pi_lambda _ fun n => hY n
  have he : Measurable (fun x : ℕ → ℝ => x 0) := measurable_pi_apply 0
  have h1 := congrArg (fun μ => Measure.map (fun x : ℕ → ℝ => x 0) μ) (hstat i)
  simp only [Measure.map_map he hmi, Measure.map_map he hm0] at h1
  have e1 : ((fun x : ℕ → ℝ => x 0) ∘ fun ω => (fun n => Y (n + i) ω)) = Y i := by
    funext ω; simp
  have e2 : ((fun x : ℕ → ℝ => x 0) ∘ fun ω => (fun n => Y n ω)) = Y 0 := by
    funext ω; simp
  rw [e1, e2] at h1
  have h0 : MemLp (id : ℝ → ℝ) 2 (Measure.map (Y 0) P) := by
    rw [memLp_map_measure_iff (by fun_prop) (hY 0).aemeasurable]
    simpa using hL2
  rw [← h1] at h0
  simpa using h0.comp_of_map (hY i).aemeasurable


end Helpers

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by
  -- the log moment puts `Y 0` in `L²`
  have hL2 : MemLp (Y 0) 2 P :=
    (MarkovChainCLT.memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  -- summable covariances give the linear growth of the variance
  have hvarlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      atTop (𝓝 (seqAsymptoticVariance P Y)) :=
    _root_.NumberLogPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum.solution P Y hY hstat hL2 hsum
  -- recoding preserves stationarity and does not increase the mixing coefficients
  have hstat_comp : ∀ g : ℝ → ℝ, Measurable g →
      IsStrictlyStationary P (fun i ω => g (Y i ω)) :=
    fun g hg => MarkovChainCLT.isStrictlyStationary_comp_of_measurable P Y hY hstat g hg
  have halpha_comp : ∀ g : ℝ → ℝ, Measurable g → ∀ n,
      alphaMixingCoef P (fun i ω => g (Y i ω)) n ≤ alphaMixingCoef P Y n :=
    fun g hg n => (MarkovChainCLT.alphaMixingCoef_comp_nonneg_le_of_finite P Y g hg n).2
  -- the fourth-moment inequality for the truncated part
  have hfourth : ∀ X : ℕ → Ω → ℝ, (∀ n, Measurable (X n)) → IsStrictlyStationary P X →
      (∫ ω, X 0 ω ∂P = 0) → ∀ M : ℝ, (∀ i, ∀ ω, |X i ω| ≤ M) →
      (∀ n, alphaMixingCoef P X n ≤ c * a ^ n) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 :=
    fun X hXm hXs hXc M hM hXa =>
      _root_.NumberLogPort_MarkovChainCLT_integral_pow_four_partialSum_le_of_bounded_of_exp_alpha.solution P X hXm hXs hXc M hM
        c a ha0 ha1 hXa
  -- the smallness of the truncated tail
  have htail : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n, (truncHigh T (Y i ω)
        - ∫ ω', truncHigh T (Y 0 ω') ∂P)) ^ 2 ∂P ≤ ε * n :=
    fun ε hε =>
      _root_.NumberLogPort_MarkovChainCLT_exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment.solution P Y hY hstat
        hcent c a ha0 ha1 hα hmom ε hε
  classical
  set σ2 : ℝ := seqAsymptoticVariance P Y with hσ2def
  set v : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P with hvdef
  have hSmeas : ∀ n : ℕ, Measurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) :=
    fun n => Finset.measurable_sum _ fun i _ => hY i
  have hYL2 : ∀ i, MemLp (Y i) 2 P := memLp_two_of_stationary P Y hY hstat hL2
  have hSL2 : ∀ n : ℕ, MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
    fun n => memLp_finsetSum _ (fun i _ => hYL2 i)
  have hSsq : ∀ n : ℕ, Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) P :=
    fun n => (hSL2 n).integrable_sq
  have hv0 : ∀ n, 0 ≤ v n := fun n => integral_nonneg fun ω => sq_nonneg _
  -- the variance of the partial sums grows linearly
  obtain ⟨N₀, hN₀1, hN₀v⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → σ2 * n / 2 ≤ v n := by
    have hev : ∀ᶠ n : ℕ in atTop, σ2 / 2 < (n : ℝ)⁻¹ * v n :=
      hvarlim.eventually (eventually_gt_nhds (by linarith))
    obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
    refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
    have h1 := (hN n (le_trans (le_max_left _ _) hn)).1
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have := mul_le_mul_of_nonneg_left h1.le hnpos.le
    rw [← mul_assoc] at this
    field_simp at this ⊢
    nlinarith [this]
  refine _root_.NumberLogPort_MeasureTheory_uniformIntegrable_one_of_sq_bounded_approx.solution P _
    (fun n => ((hSmeas n).pow_const 2).div_const _)
    (fun n ω => div_nonneg (sq_nonneg _) (hv0 n)) (fun n => (hSsq n).div_const _)
    (fun n => by rw [integral_div]; exact div_self_le_one _) ?_
  intro ε hε
  -- choose the truncation level
  obtain ⟨T, hT0, hTb⟩ := htail (ε * σ2 / 4) (by positivity)
  set m : ℝ := ∫ ω, truncLow T (Y 0 ω) ∂P with hmdef
  set mt : ℝ := ∫ ω, truncHigh T (Y 0 ω) ∂P with hmtdef
  set X : ℕ → Ω → ℝ := fun i ω => truncLow T (Y i ω) - m with hXdef
  set Z : ℕ → Ω → ℝ := fun i ω => truncHigh T (Y i ω) - mt with hZdef
  have hlowmeas : ∀ i, Measurable (fun ω => truncLow T (Y i ω)) :=
    fun i => (measurable_truncLow T).comp (hY i)
  have hhighmeas : ∀ i, Measurable (fun ω => truncHigh T (Y i ω)) :=
    fun i => (measurable_truncHigh T).comp (hY i)
  have hlowint : ∀ i, Integrable (fun ω => truncLow T (Y i ω)) P := by
    intro i
    refine Integrable.mono' (integrable_const T) (hlowmeas i).aestronglyMeasurable ?_
    exact Eventually.of_forall fun ω => by
      simpa using abs_truncLow_le hT0.le (Y i ω)
  have hYint : ∀ i, Integrable (Y i) P := fun i => (hYL2 i).integrable (by norm_num)
  have hhighint : ∀ i, Integrable (fun ω => truncHigh T (Y i ω)) P := by
    intro i
    have : (fun ω => truncHigh T (Y i ω)) = fun ω => Y i ω - truncLow T (Y i ω) := by
      funext ω
      have := truncLow_add_truncHigh T (Y i ω)
      linarith
    rw [this]
    exact (hYint i).sub (hlowint i)
  have hmmt : m + mt = 0 := by
    rw [hmdef, hmtdef, ← integral_add (hlowint 0) (hhighint 0)]
    rw [← hcent]
    exact integral_congr_ae (Eventually.of_forall fun ω => truncLow_add_truncHigh T (Y 0 ω))
  have hXmeas : ∀ i, Measurable (X i) := fun i => (hlowmeas i).sub measurable_const
  have hZmeas : ∀ i, Measurable (Z i) := fun i => (hhighmeas i).sub measurable_const
  have hXcent : ∫ ω, X 0 ω ∂P = 0 := by
    rw [hXdef]
    simp only
    rw [integral_sub (hlowint 0) (integrable_const m)]
    simp [← hmdef]
  have hXbdd : ∀ i, ∀ ω, |X i ω| ≤ T + |m| := by
    intro i ω
    calc |X i ω| ≤ |truncLow T (Y i ω)| + |m| := by
          simpa [hXdef] using abs_sub (truncLow T (Y i ω)) m
      _ ≤ T + |m| := by linarith [abs_truncLow_le hT0.le (Y i ω)]
  have hXstat : IsStrictlyStationary P X :=
    hstat_comp (fun x => truncLow T x - m) ((measurable_truncLow T).sub measurable_const)
  have hXalpha : ∀ n, alphaMixingCoef P X n ≤ c * a ^ n := fun n =>
    le_trans (halpha_comp (fun x => truncLow T x - m)
      ((measurable_truncLow T).sub measurable_const) n) (hα n)
  obtain ⟨K, hK0, hKb⟩ := hfourth X hXmeas hXstat hXcent (T + |m|) hXbdd hXalpha
  -- the two halves of the partial sum
  set A : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, X i ω with hAdef
  set B : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, Z i ω with hBdef
  have hsplit : ∀ n ω, (∑ i ∈ Finset.range n, Y i ω) = A n ω + B n ω := by
    intro n ω
    rw [hAdef, hBdef]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := truncLow_add_truncHigh T (Y i ω)
    simp only [hXdef, hZdef]
    linarith
  have hAmeas : ∀ n, Measurable (A n) := fun n => Finset.measurable_sum _ fun i _ => hXmeas i
  have hBmeas : ∀ n, Measurable (B n) := fun n => Finset.measurable_sum _ fun i _ => hZmeas i
  have hAbdd : ∀ n, ∀ ω, |A n ω| ≤ n * (T + |m|) := by
    intro n ω
    calc |A n ω| ≤ ∑ i ∈ Finset.range n, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (T + |m|) :=
          Finset.sum_le_sum fun i _ => hXbdd i ω
      _ = n * (T + |m|) := by simp [Finset.sum_const, nsmul_eq_mul, mul_add]
  have hZL2 : ∀ i, MemLp (Z i) 2 P := by
    intro i
    have h1 : MemLp (fun ω => truncHigh T (Y i ω)) 2 P := by
      have heq : (fun ω => truncHigh T (Y i ω)) = fun ω => Y i ω - truncLow T (Y i ω) := by
        funext ω
        have := truncLow_add_truncHigh T (Y i ω)
        linarith
      rw [heq]
      refine (hYL2 i).sub ?_
      refine MemLp.of_bound (hlowmeas i).aestronglyMeasurable T ?_
      exact Eventually.of_forall fun ω => by
        simpa using abs_truncLow_le hT0.le (Y i ω)
    exact h1.sub (memLp_const mt)
  have hBL2 : ∀ n, MemLp (B n) 2 P := fun n => memLp_finsetSum _ (fun i _ => hZL2 i)
  refine ⟨N₀, fun n ω => 2 * (A n ω) ^ 2 / v n, fun n ω => 2 * (B n ω) ^ 2 / v n,
    16 * K / σ2 ^ 2, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the truncated part is bounded, hence in `L²`
    intro n _
    refine MemLp.of_bound ((((hAmeas n).pow_const 2).const_mul 2).div_const
      (v n)).aestronglyMeasurable (2 * ((n : ℝ) * (T + |m|)) ^ 2 / v n) ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hv0 n)]
    gcongr
    rw [abs_of_nonneg (by positivity)]
    have h1 : |A n ω| ≤ (n : ℝ) * (T + |m|) := hAbdd n ω
    have h2 : (A n ω) ^ 2 ≤ ((n : ℝ) * (T + |m|)) ^ 2 := by
      nlinarith [sq_abs (A n ω), abs_nonneg (A n ω)]
    linarith
  · -- the tail part is integrable
    intro n _
    exact (((hBL2 n).integrable_sq).const_mul 2).div_const _
  · exact fun n _ ω => by positivity
  · exact fun n _ ω => by positivity
  · -- the pointwise domination `(A + B)² ≤ 2A² + 2B²`
    intro n _ ω
    show (∑ i ∈ Finset.range n, Y i ω) ^ 2 / v n
      ≤ 2 * (A n ω) ^ 2 / v n + 2 * (B n ω) ^ 2 / v n
    rw [hsplit n ω]
    rcases eq_or_lt_of_le (hv0 n) with h | h
    · simp [← h]
    · have hr : 2 * (A n ω) ^ 2 / v n + 2 * (B n ω) ^ 2 / v n
          = (2 * (A n ω) ^ 2 + 2 * (B n ω) ^ 2) / v n := by ring
      rw [hr, div_le_div_iff_of_pos_right h]
      nlinarith [sq_nonneg (A n ω - B n ω)]
  · -- the `L²` bound for the truncated part
    intro n hn
    have hvpos : 0 < v n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have := hN₀v n hn
      nlinarith
    have hvlow : σ2 * n / 2 ≤ v n := hN₀v n hn
    have heq : ∀ ω, (2 * (A n ω) ^ 2 / v n) ^ 2 = 4 / v n ^ 2 * (A n ω) ^ 4 := by
      intro ω; field_simp; ring
    rw [integral_congr_ae (Eventually.of_forall heq), integral_const_mul]
    have h4 : ∫ ω, (A n ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 := hKb n
    have hnpos : (0 : ℝ) < n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      exact_mod_cast hn1
    have hsq : (σ2 * n / 2) ^ 2 ≤ v n ^ 2 := by
      have h0 : 0 ≤ σ2 * n / 2 := by positivity
      nlinarith
    have hint0 : 0 ≤ ∫ ω, (A n ω) ^ 4 ∂P := by
      refine integral_nonneg fun ω => by positivity
    calc 4 / v n ^ 2 * ∫ ω, (A n ω) ^ 4 ∂P
        ≤ 4 / (σ2 * n / 2) ^ 2 * (K * (n : ℝ) ^ 2) := by
          gcongr
      _ = 16 * K / σ2 ^ 2 := by field_simp; ring
  · -- the `L¹` bound for the tail part
    intro n hn
    have hvlow : σ2 * n / 2 ≤ v n := hN₀v n hn
    have hnpos : (0 : ℝ) < n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      exact_mod_cast hn1
    have hvpos : 0 < v n := by nlinarith
    have hB : ∫ ω, (B n ω) ^ 2 ∂P ≤ ε * σ2 / 4 * n := hTb n
    have hB0 : 0 ≤ ∫ ω, (B n ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have heq : ∫ ω, 2 * (B n ω) ^ 2 / v n ∂P = 2 / v n * ∫ ω, (B n ω) ^ 2 ∂P := by
      have : ∀ ω, 2 * (B n ω) ^ 2 / v n = 2 / v n * (B n ω) ^ 2 := by
        intro ω; field_simp
      rw [integral_congr_ae (Eventually.of_forall this), integral_const_mul]
    rw [heq]
    calc 2 / v n * ∫ ω, (B n ω) ^ 2 ∂P ≤ 2 / (σ2 * n / 2) * (ε * σ2 / 4 * n) := by
          gcongr
      _ = ε := by field_simp; ring

end NumberLogPort_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment


namespace NumberLogPort_MarkovChainCLT_tendstoInDistribution_of_exp_alpha_of_log_moment

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  set sig : ℝ := seqAsymptoticVariance P Y with hsig
  set v : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P with hv
  -- Step 0: the log-moment hypothesis puts `Y 0` in `L²`.
  have hL2 : MemLp (Y 0) 2 P :=
    (MarkovChainCLT.memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  -- Step 1: the strong mixing coefficients tend to `0`, being squeezed by `c aⁿ`.
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
  have hα0 : Tendsto (fun n => alphaMixingCoef P Y n) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun n : ℕ => c * a ^ n) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
      simpa using this.const_mul c
    exact squeeze_zero hα_nonneg hα hgeo
  -- Step 2: the variance of the partial sums grows linearly with slope `σ² > 0`.
  have hC1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * v n) atTop (𝓝 sig) :=
    _root_.NumberLogPort_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum.solution P Y hY hstat hL2 hsum
  have hvtop : Tendsto v atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (sig / 2)) atTop atTop :=
      hn.atTop_mul_const (by positivity)
    refine tendsto_atTop_mono' atTop ?_ hlin
    have hev : ∀ᶠ n : ℕ in atTop, sig / 2 < (n : ℝ)⁻¹ * v n :=
      hC1.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [hev, eventually_gt_atTop 0] with n hn1 hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have : (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) :=
      mul_le_mul_of_nonneg_left hn1.le hnpos.le
    calc (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) := this
      _ = v n := by field_simp
  -- Step 3: the CLT for the self-normalized sums, from Theorem 3 and uniform integrability.
  have hUI := _root_.NumberLogPort_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment.solution
    P Y hY hstat hcent c a ha0 ha1 hα hmom hsum hvar
  have hnorm := (MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing P Y hY hstat hcent
    hL2 hα0 hvtop).2 hUI
  -- Step 4: change the normalisation from `σ_n` to `√n`.
  have hs : 0 < Real.sqrt sig := Real.sqrt_pos.2 hvar
  have hd : Tendsto (fun n : ℕ => Real.sqrt (v n) / Real.sqrt n) atTop (𝓝 (Real.sqrt sig)) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)⁻¹ * v n)) atTop (𝓝 (Real.sqrt sig)) :=
      (Real.continuous_sqrt.tendsto sig).comp hC1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hvtop.eventually_ge_atTop 0] with n hn0 hvn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
    ring
  have hXmeas : ∀ n : ℕ, Measurable fun ω => ∑ i ∈ Finset.range n, Y i ω :=
    fun n => Finset.measurable_sum _ fun i _ => hY i
  have hfin := _root_.NumberLogPort_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized.solution P
    (fun n ω => ∑ i ∈ Finset.range n, Y i ω) (fun n => Real.sqrt (v n)) (Real.sqrt sig) hs
    hXmeas hd hnorm
  have hsq : Real.toNNReal (Real.sqrt sig ^ 2) = sig.toNNReal := by
    rw [Real.sq_sqrt hvar.le]
  rwa [hsq] at hfin

end NumberLogPort_MarkovChainCLT_tendstoInDistribution_of_exp_alpha_of_log_moment

section OwnCandidate

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 6 (Doukhan–Massart–Rio), reduced to the covariance-summability
and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := _root_.NumberLogPort_MarkovChainCLT_summable_covariance_of_exp_alpha_of_log_moment.solution
    P Y hY hstat hcent c a ha0 ha1 hα hmom
  refine ⟨hsum, fun hvar => ?_⟩
  exact _root_.NumberLogPort_MarkovChainCLT_tendstoInDistribution_of_exp_alpha_of_log_moment.solution
    P Y hY hstat hcent c a ha0 ha1 hα hmom hsum hvar

end OwnCandidate
#print axioms solution