-- Prove2me | solution 1 for MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:38:09.37609+00:00
-- url     : https://prove2.me/submissions/2e339510-ba0b-43ee-93bb-a2390ac61cd8

import Definitions.Def_MixingCoefficients
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NumberCLTPort_LayerCake_bounded_layercake_identity

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

end NumberCLTPort_LayerCake_bounded_layercake_identity


namespace NumberCLTPort_LayerCake_expectation_add_const

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
    fun ω => _root_.NumberCLTPort_LayerCake_bounded_layercake_identity.solution (W ω) M (hWb ω)
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

end NumberCLTPort_LayerCake_expectation_add_const


namespace NumberCLTPort_ProbabilityTheory_cov_indicator_eq

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

end NumberCLTPort_ProbabilityTheory_cov_indicator_eq


namespace NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable

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

end NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable


namespace NumberCLTPort_MarkovChainCLT_alpha_indicator_cov_le

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

end NumberCLTPort_MarkovChainCLT_alpha_indicator_cov_le


namespace NumberCLTPort_MarkovChainCLT_alpha_cov_bounded

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
    _root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    _root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _
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
    fun t s => _root_.NumberCLTPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y n k _ _ (hAt t) (hBs s)
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
    fun ω => _root_.NumberCLTPort_LayerCake_bounded_layercake_identity.solution (U ω) M (hUb ω)
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
    _root_.NumberCLTPort_LayerCake_expectation_add_const.solution P V hVm M (fun ω => hVb ω)
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
      _root_.NumberCLTPort_LayerCake_bounded_layercake_identity.solution (V ω) M (hVb ω)
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
      _root_.NumberCLTPort_ProbabilityTheory_cov_indicator_eq.solution P _ _ (hAt_amb q.1) (hBs_amb q.2)
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


end NumberCLTPort_MarkovChainCLT_alpha_cov_bounded

section OwnCandidate

section DenkerComponent1

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

def partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, Y i ω

def blockSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (a n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, Y (i + a) ω

noncomputable def variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, partialSum Y n ω ^ 2 ∂P

noncomputable def sigma {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (variance P Y n)

noncomputable def normalizedSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => partialSum Y n ω / sigma P Y n

end DenkerCLT

end DenkerComponent1

section DenkerComponent2

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem partialSum_measurable (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    Measurable (partialSum Y n) := Finset.measurable_sum _ (fun i _ => hY i)

theorem blockSum_measurable (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (a n : ℕ) :
    Measurable (blockSum Y a n) := Finset.measurable_sum _ (fun i _ => hY (i + a))

theorem stationary_block_law (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (a n : ℕ) :
    P.map (blockSum Y a n) = P.map (partialSum Y n) := by
  let f : (ℕ → ℝ) → ℝ := fun z => ∑ i ∈ Finset.range n, z i
  have hf : Measurable f := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have h := congrArg (Measure.map f) (hstat a)
  rw [Measure.map_map hf (measurable_pi_lambda _ fun i => hY (i + a)),
    Measure.map_map hf (measurable_pi_lambda _ hY)] at h
  exact h

theorem stationary_block_integral (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (g : ℝ → ℝ) (hg : Measurable g) (a n : ℕ) :
    ∫ ω, g (blockSum Y a n ω) ∂P = ∫ ω, g (partialSum Y n ω) ∂P := by
  rw [← integral_map (blockSum_measurable Y hY a n).aemeasurable hg.aestronglyMeasurable,
    stationary_block_law P Y hY hstat a n,
    integral_map (partialSum_measurable Y hY n).aemeasurable hg.aestronglyMeasurable]

theorem stationary_coordinate_law (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (a : ℕ) :
    P.map (Y a) = P.map (Y 0) := by
  have hb : blockSum Y a 1 = Y a := by funext ω; simp [blockSum]
  have hp : partialSum Y 1 = Y 0 := by funext ω; simp [partialSum]
  simpa only [hb, hp] using stationary_block_law P Y hY hstat a 1

theorem stationary_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : MemLp (Y n) 2 P := by
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hY 0).aemeasurable).2 hL2
  have hn : MemLp (id : ℝ → ℝ) 2 (P.map (Y n)) := by
    rw [stationary_coordinate_law P Y hY hstat n]
    exact h0
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hY n).aemeasurable).1 hn

theorem partialSum_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : MemLp (partialSum Y n) 2 P :=
  memLp_finsetSum _ (fun i _ => stationary_memLp P Y hY hstat hL2 i)

theorem blockSum_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (a n : ℕ) : MemLp (blockSum Y a n) 2 P :=
  memLp_finsetSum _ (fun i _ => stationary_memLp P Y hY hstat hL2 (i + a))

theorem coordinate_integral_zero (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (n : ℕ) : ∫ ω, Y n ω ∂P = 0 := by
  have h := stationary_block_integral P Y hY hstat id measurable_id n 1
  simpa [blockSum, partialSum, hcent] using h

theorem partialSum_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    ∫ ω, partialSum Y n ω ∂P = 0 := by
  change (∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P) = 0
  rw [integral_finsetSum _ (fun i _ => (stationary_memLp P Y hY hstat hL2 i).integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun i _ => coordinate_integral_zero P Y hY hstat hcent i)

theorem variance_nonneg (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) : 0 ≤ variance P Y n :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem sigma_nonneg (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) : 0 ≤ sigma P Y n :=
  Real.sqrt_nonneg _

theorem sigma_sq (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) :
    sigma P Y n ^ 2 = variance P Y n := Real.sq_sqrt (variance_nonneg P Y n)

theorem normalizedSum_measurable (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) : Measurable (normalizedSum P Y n) :=
  (partialSum_measurable Y hY n).div_const _

theorem normalizedSum_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : MemLp (normalizedSum P Y n) 2 P := by
  unfold normalizedSum
  simpa only [div_eq_mul_inv] using
    (partialSum_memLp P Y hY hstat hL2 n).mul_const (sigma P Y n)⁻¹

theorem normalizedSum_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    ∫ ω, normalizedSum P Y n ω ∂P = 0 := by
  simp only [normalizedSum, integral_div, partialSum_integral_zero P Y hY hstat hcent hL2 n,
    zero_div]

theorem normalizedSum_sq (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    normalizedSum P Y n ω ^ 2 = partialSum Y n ω ^ 2 / variance P Y n := by
  rw [normalizedSum, div_pow, sigma_sq]

theorem normalizedSum_second_moment (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) :
    ∫ ω, normalizedSum P Y n ω ^ 2 ∂P = variance P Y n / variance P Y n := by
  simp only [normalizedSum_sq, integral_div, variance]

theorem normalizedSum_second_moment_le_one (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) :
    ∫ ω, normalizedSum P Y n ω ^ 2 ∂P ≤ 1 := by
  rw [normalizedSum_second_moment]
  by_cases h : variance P Y n = 0
  · simp [h]
  · rw [div_self h]

end DenkerCLT

end DenkerComponent2

section DenkerComponent3

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}

noncomputable def secondNorm (P : Measure Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ ω, f ω ^ 2 ∂P)

theorem secondNorm_nonneg (P : Measure Ω) (f : Ω → ℝ) : 0 ≤ secondNorm P f :=
  Real.sqrt_nonneg _

theorem secondNorm_congr_ae (h : f =ᵐ[P] g) : secondNorm P f = secondNorm P g := by
  unfold secondNorm
  congr 1
  exact integral_congr_ae (h.mono fun _ hfg => congrArg (fun x : ℝ => x ^ 2) hfg)

theorem toLp_inner_eq_integral_mul (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [Real.inner_apply, hfω, hgω]

theorem toLp_norm_sq_eq_integral_sq (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, toLp_inner_eq_integral_mul hf hf]
  simp only [pow_two]

theorem secondNorm_eq_norm_toLp (hf : MemLp f 2 P) :
    secondNorm P f = ‖hf.toLp f‖ := by
  rw [secondNorm, ← toLp_norm_sq_eq_integral_sq hf, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

theorem secondNorm_sq (hf : MemLp f 2 P) :
    secondNorm P f ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [secondNorm_eq_norm_toLp hf, toLp_norm_sq_eq_integral_sq hf]

@[simp] theorem secondNorm_zero (P : Measure Ω) : secondNorm P (fun _ => (0 : ℝ)) = 0 := by
  simp [secondNorm]

@[simp] theorem secondNorm_abs (P : Measure Ω) (f : Ω → ℝ) :
    secondNorm P (fun ω => |f ω|) = secondNorm P f := by
  simp only [secondNorm, sq_abs]

@[simp] theorem secondNorm_neg (P : Measure Ω) (f : Ω → ℝ) :
    secondNorm P (fun ω => -f ω) = secondNorm P f := by
  simp only [secondNorm, neg_sq]

theorem secondNorm_add_le (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    secondNorm P (fun ω => f ω + g ω) ≤ secondNorm P f + secondNorm P g := by
  change secondNorm P (f + g) ≤ secondNorm P f + secondNorm P g
  rw [secondNorm_eq_norm_toLp (hf.add hg), secondNorm_eq_norm_toLp hf,
    secondNorm_eq_norm_toLp hg]
  exact norm_add_le (hf.toLp f) (hg.toLp g)

theorem secondNorm_sub_le (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    secondNorm P (fun ω => f ω - g ω) ≤ secondNorm P f + secondNorm P g := by
  change secondNorm P (f - g) ≤ secondNorm P f + secondNorm P g
  rw [secondNorm_eq_norm_toLp (hf.sub hg), secondNorm_eq_norm_toLp hf,
    secondNorm_eq_norm_toLp hg]
  exact norm_sub_le (hf.toLp f) (hg.toLp g)

theorem abs_secondNorm_sub_le (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |secondNorm P f - secondNorm P g| ≤ secondNorm P (fun ω => f ω - g ω) := by
  change |secondNorm P f - secondNorm P g| ≤ secondNorm P (f - g)
  rw [secondNorm_eq_norm_toLp (hf.sub hg), secondNorm_eq_norm_toLp hf,
    secondNorm_eq_norm_toLp hg]
  exact abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g)

theorem secondNorm_mono (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (h : ∀ᵐ ω ∂P, |f ω| ≤ |g ω|) : secondNorm P f ≤ secondNorm P g := by
  apply Real.sqrt_le_sqrt
  apply integral_mono_ae hf.integrable_sq hg.integrable_sq
  filter_upwards [h] with ω hω
  nlinarith [sq_abs (f ω), sq_abs (g ω), abs_nonneg (f ω), abs_nonneg (g ω)]

theorem secondNorm_const_mul (P : Measure Ω) (c : ℝ) (f : Ω → ℝ) :
    secondNorm P (fun ω => c * f ω) = |c| * secondNorm P f := by
  simp only [secondNorm, mul_pow, integral_const_mul,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem secondNorm_div_const (P : Measure Ω) (f : Ω → ℝ) (c : ℝ) :
    secondNorm P (fun ω => f ω / c) = secondNorm P f / |c| := by
  simp only [div_eq_mul_inv, mul_comm (f _) c⁻¹]
  rw [secondNorm_const_mul]
  simp only [abs_inv, mul_comm]

theorem secondNorm_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ i ∈ s, MemLp (F i) 2 P) :
    secondNorm P (fun ω => ∑ i ∈ s, F i ω) ≤ ∑ i ∈ s, secondNorm P (F i) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      intro hF
      have hs : ∀ j ∈ s, MemLp (F j) 2 P := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      exact (secondNorm_add_le (hF i (Finset.mem_insert_self i s))
        (memLp_finsetSum s hs)).trans (add_le_add le_rfl (ih hs))

theorem abs_integral_mul_le_secondNorm (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤ secondNorm P f * secondNorm P g := by
  rw [← toLp_inner_eq_integral_mul hf hg, secondNorm_eq_norm_toLp hf,
    secondNorm_eq_norm_toLp hg]
  exact abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)

theorem secondNorm_const [IsProbabilityMeasure P] (c : ℝ) :
    secondNorm P (fun _ => c) = |c| := by
  simp [secondNorm, Real.sqrt_sq_eq_abs]

theorem abs_integral_le_secondNorm [IsProbabilityMeasure P] (hf : MemLp f 2 P) :
    |∫ ω, f ω ∂P| ≤ secondNorm P f := by
  simpa only [mul_one, secondNorm_const, abs_one] using
    abs_integral_mul_le_secondNorm hf (memLp_const (1 : ℝ))

theorem integral_abs_le_secondNorm [IsProbabilityMeasure P] (hf : MemLp f 2 P) :
    (∫ ω, |f ω| ∂P) ≤ secondNorm P f := by
  have h := abs_integral_le_secondNorm hf.norm
  simp only [Real.norm_eq_abs, secondNorm_abs] at h
  exact (le_abs_self _).trans h

theorem abs_covariance_le_two_secondNorm [IsProbabilityMeasure P]
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |cov[f, g; P]| ≤ 2 * secondNorm P f * secondNorm P g := by
  rw [covariance_eq_sub hf hg]
  calc
    |(∫ ω, (f * g) ω ∂P) - (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P| ≤
        |∫ ω, f ω * g ω ∂P| + |∫ ω, f ω ∂P| * |∫ ω, g ω ∂P| := by
          simpa only [abs_mul, Pi.mul_apply] using
            abs_sub (∫ ω, (f * g) ω ∂P) ((∫ ω, f ω ∂P) * ∫ ω, g ω ∂P)
    _ ≤ secondNorm P f * secondNorm P g + secondNorm P f * secondNorm P g :=
      add_le_add (abs_integral_mul_le_secondNorm hf hg)
        (mul_le_mul (abs_integral_le_secondNorm hf) (abs_integral_le_secondNorm hg)
          (abs_nonneg _) (secondNorm_nonneg P f))
    _ = 2 * secondNorm P f * secondNorm P g := by ring

end DenkerCLT

end DenkerComponent3

section DenkerComponent4

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem secondNorm_blockSum (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (a n : ℕ) :
    secondNorm P (blockSum Y a n) = sigma P Y n := by
  unfold secondNorm sigma variance
  rw [stationary_block_integral P Y hY hstat (fun x => x ^ 2)
    (measurable_id.pow_const 2) a n]

theorem secondNorm_coordinate (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (a : ℕ) :
    secondNorm P (Y a) = secondNorm P (Y 0) := by
  simpa [blockSum, sigma, variance, partialSum, secondNorm] using
    secondNorm_blockSum P Y hY hstat a 1

theorem secondNorm_blockSum_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (a n : ℕ) :
    secondNorm P (blockSum Y a n) ≤ (n : ℝ) * secondNorm P (Y 0) := by
  unfold blockSum
  have h := secondNorm_finset_sum (P := P) (Finset.range n) (fun i => Y (i + a))
    (fun i _ => stationary_memLp P Y hY hstat hL2 (i + a))
  simpa only [blockSum, secondNorm_coordinate P Y hY hstat, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] using h

theorem secondNorm_partialSum_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    secondNorm P (partialSum Y n) ≤ (n : ℝ) * secondNorm P (Y 0) := by
  unfold partialSum
  have h := secondNorm_blockSum_le P Y hY hstat hL2 0 n
  unfold blockSum at h
  simpa only [Nat.add_zero] using h

omit [MeasurableSpace Ω] in
theorem blockSum_add_length (Y : ℕ → Ω → ℝ) (a m n : ℕ) :
    blockSum Y a (m + n) = fun ω => blockSum Y a m ω + blockSum Y (a + m) n ω := by
  funext ω
  simp only [blockSum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

omit [MeasurableSpace Ω] in
theorem blockSum_shift_difference (Y : ℕ → Ω → ℝ) (a b m : ℕ) :
    (fun ω => blockSum Y (a + b) m ω - blockSum Y a m ω) =
      fun ω => blockSum Y (a + m) b ω - blockSum Y a b ω := by
  funext ω
  have hbm := congrFun (blockSum_add_length Y a b m) ω
  have hmb := congrFun (blockSum_add_length Y a m b) ω
  rw [Nat.add_comm b m] at hbm
  linarith

theorem secondNorm_blockSum_shift_sub_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (a b m : ℕ) :
    secondNorm P (fun ω => blockSum Y (a + b) m ω - blockSum Y a m ω) ≤
      2 * (b : ℝ) * secondNorm P (Y 0) := by
  rw [blockSum_shift_difference]
  calc
    _ ≤ secondNorm P (blockSum Y (a + m) b) + secondNorm P (blockSum Y a b) :=
      secondNorm_sub_le (blockSum_memLp P Y hY hstat hL2 (a + m) b)
        (blockSum_memLp P Y hY hstat hL2 a b)
    _ ≤ (b : ℝ) * secondNorm P (Y 0) + (b : ℝ) * secondNorm P (Y 0) :=
      add_le_add (secondNorm_blockSum_le P Y hY hstat hL2 (a + m) b)
        (secondNorm_blockSum_le P Y hY hstat hL2 a b)
    _ = _ := by ring

omit [MeasurableSpace Ω] in
theorem sum_consecutive_blocks (Y : ℕ → Ω → ℝ) (k m : ℕ) :
    (fun ω => ∑ j ∈ Finset.range k, blockSum Y (j * m) m ω) = partialSum Y (k * m) := by
  induction k with
  | zero => funext ω; simp [partialSum]
  | succ k ih =>
      funext ω
      have hb := congrFun (blockSum_add_length Y 0 (k * m) m) ω
      rw [Finset.sum_range_succ, congrFun ih ω, Nat.succ_mul]
      simpa only [blockSum, partialSum, Nat.add_zero, Nat.zero_add] using hb.symm

def separatedSum (Y : ℕ → Ω → ℝ) (k m q : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range k, blockSum Y (j * (m + q)) m ω

theorem separatedSum_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (k m q : ℕ) : MemLp (separatedSum Y k m q) 2 P :=
  memLp_finsetSum _ (fun j _ => blockSum_memLp P Y hY hstat hL2 (j * (m + q)) m)

omit [MeasurableSpace Ω] in
theorem separatedSum_sub_partialSum (Y : ℕ → Ω → ℝ) (k m q : ℕ) :
    (fun ω => separatedSum Y k m q ω - partialSum Y (k * m) ω) =
      fun ω => ∑ j ∈ Finset.range k,
        (blockSum Y (j * (m + q)) m ω - blockSum Y (j * m) m ω) := by
  funext ω
  rw [← congrFun (sum_consecutive_blocks Y k m) ω]
  simp only [separatedSum, Finset.sum_sub_distrib]

theorem secondNorm_separatedSum_sub_partialSum_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (k m q : ℕ) :
    secondNorm P (fun ω => separatedSum Y k m q ω - partialSum Y (k * m) ω) ≤
      2 * (k : ℝ) ^ 2 * (q : ℝ) * secondNorm P (Y 0) := by
  rw [separatedSum_sub_partialSum]
  have hmem : ∀ j ∈ Finset.range k,
      MemLp (fun ω => blockSum Y (j * (m + q)) m ω - blockSum Y (j * m) m ω) 2 P :=
    fun j _ => (blockSum_memLp P Y hY hstat hL2 _ _).sub
      (blockSum_memLp P Y hY hstat hL2 _ _)
  refine (secondNorm_finset_sum _ _ hmem).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.range k, 2 * (k : ℝ) * (q : ℝ) * secondNorm P (Y 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
      have hb := secondNorm_blockSum_shift_sub_le P Y hY hstat hL2 (j * m) (j * q) m
      rw [← Nat.mul_add] at hb
      push_cast at hb
      have hc : 0 ≤ (q : ℝ) * secondNorm P (Y 0) :=
        mul_nonneg (Nat.cast_nonneg q) (secondNorm_nonneg P (Y 0))
      have hjkc := mul_le_mul_of_nonneg_right hjk hc
      exact hb.trans (by nlinarith)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

omit [MeasurableSpace Ω] in
theorem partialSum_division_remainder (Y : ℕ → Ω → ℝ) (n k : ℕ) :
    (fun ω => partialSum Y n ω - partialSum Y (k * (n / k)) ω) =
      blockSum Y (k * (n / k)) (n % k) := by
  have hn : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hb := blockSum_add_length Y 0 (k * (n / k)) (n % k)
  rw [hn] at hb
  funext ω
  have h : partialSum Y n ω = partialSum Y (k * (n / k)) ω +
      blockSum Y (k * (n / k)) (n % k) ω := by
    simpa only [blockSum, partialSum, Nat.add_zero, Nat.zero_add] using congrFun hb ω
  linarith

theorem secondNorm_partialSum_division_sub_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n k : ℕ) (hk : 0 < k) :
    secondNorm P (fun ω => partialSum Y n ω - partialSum Y (k * (n / k)) ω) ≤
      (k : ℝ) * secondNorm P (Y 0) := by
  rw [partialSum_division_remainder]
  refine (secondNorm_blockSum_le P Y hY hstat hL2 _ _).trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (Nat.le_of_lt (Nat.mod_lt n hk))) (secondNorm_nonneg P (Y 0))

theorem secondNorm_separatedSum_sub_partialSum_div_le (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n k q : ℕ) (hk : 0 < k) :
    secondNorm P (fun ω => separatedSum Y k (n / k) q ω - partialSum Y n ω) ≤
      (2 * (k : ℝ) ^ 2 * (q : ℝ) + (k : ℝ)) * secondNorm P (Y 0) := by
  have heq : (fun ω => separatedSum Y k (n / k) q ω - partialSum Y n ω) =
      fun ω => (separatedSum Y k (n / k) q ω - partialSum Y (k * (n / k)) ω) +
        -(partialSum Y n ω - partialSum Y (k * (n / k)) ω) := by
    funext ω
    ring
  rw [heq]
  refine (secondNorm_add_le
    ((separatedSum_memLp P Y hY hstat hL2 _ _ _).sub
      (partialSum_memLp P Y hY hstat hL2 _))
    (((partialSum_memLp P Y hY hstat hL2 _).sub
      (partialSum_memLp P Y hY hstat hL2 _)).neg)).trans ?_
  change secondNorm P (fun ω => separatedSum Y k (n / k) q ω - partialSum Y (k * (n / k)) ω) +
    secondNorm P (fun ω => -(partialSum Y n ω - partialSum Y (k * (n / k)) ω)) ≤ _
  rw [secondNorm_neg]
  calc
    _ ≤ 2 * (k : ℝ) ^ 2 * (q : ℝ) * secondNorm P (Y 0) +
        (k : ℝ) * secondNorm P (Y 0) :=
      add_le_add (secondNorm_separatedSum_sub_partialSum_le P Y hY hstat hL2 _ _ _)
        (secondNorm_partialSum_division_sub_le P Y hY hstat hL2 n k hk)
    _ = _ := by ring

end DenkerCLT

end DenkerComponent4

section DenkerComponent5

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology

namespace DenkerCLT

noncomputable def cfRemainder (a : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * I) - 1 - (a : ℂ) * I + (a : ℂ) ^ 2 / 2

lemma norm_cfRemainder_le_cube {a : ℝ} (ha : |a| ≤ 1) :
    ‖cfRemainder a‖ ≤ |a| ^ 3 := by
  have heq : (∑ m ∈ Finset.range 3, ((a : ℂ) * I) ^ m / m.factorial) =
      1 + (a : ℂ) * I - (a : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, mul_pow]
    ring
  have h := Complex.exp_bound (x := (a : ℂ) * I) (by simpa using ha)
    (n := 3) (by decide)
  rw [heq] at h
  have hr : cfRemainder a =
      Complex.exp ((a : ℂ) * I) - (1 + (a : ℂ) * I - (a : ℂ) ^ 2 / 2) := by
    unfold cfRemainder
    ring
  rw [hr]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at h
  norm_num [Nat.factorial] at h
  nlinarith [pow_nonneg (abs_nonneg a) 3]

lemma norm_cfRemainder_le_square (a : ℝ) : ‖cfRemainder a‖ ≤ 4 * a ^ 2 := by
  by_cases ha : |a| ≤ 1
  · have h := norm_cfRemainder_le_cube ha
    have hsq := sq_abs a
    have hmul : |a| * |a| ^ 2 ≤ |a| ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) ha
    nlinarith [sq_nonneg a]
  · have ha' : 1 < |a| := lt_of_not_ge ha
    have h : ‖cfRemainder a‖ ≤ 2 + |a| + a ^ 2 / 2 := by
      calc
        ‖cfRemainder a‖ ≤
            ‖Complex.exp ((a : ℂ) * I) - 1 - (a : ℂ) * I‖ + ‖(a : ℂ) ^ 2 / 2‖ :=
          norm_add_le _ _
        _ ≤ (‖Complex.exp ((a : ℂ) * I)‖ + ‖(1 : ℂ)‖ + ‖(a : ℂ) * I‖) +
            ‖(a : ℂ) ^ 2 / 2‖ := by
          grw [norm_sub_le, norm_sub_le]
        _ = 2 + |a| + a ^ 2 / 2 := by
          simp [norm_pow, sq_abs]
          ring
    nlinarith [sq_abs a, sq_nonneg (|a| - 1)]

lemma norm_cfRemainder_mul_le {u x K : ℝ} (_hK : 0 ≤ K) (hx : |x| ≤ K)
    (hu : |u| * K ≤ 1) :
    ‖cfRemainder (u * x)‖ ≤ u ^ 2 * (|u| * K * x ^ 2) := by
  have hux : |u * x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hu
  calc
    ‖cfRemainder (u * x)‖ ≤ |u * x| ^ 3 := norm_cfRemainder_le_cube hux
    _ = u ^ 2 * (|u| * |x| * x ^ 2) := by
      rw [abs_mul, mul_pow]
      calc
        |u| ^ 3 * |x| ^ 3 = |u| ^ 2 * (|u| * |x| * |x| ^ 2) := by ring
        _ = u ^ 2 * (|u| * |x| * x ^ 2) := by rw [sq_abs, sq_abs]
    _ ≤ u ^ 2 * (|u| * K * x ^ 2) := by gcongr

private lemma integral_nonneg_le_of_eLpNorm_one_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f P) (hfn : ∀ ω, 0 ≤ f ω) {b : ℝ} (hb : 0 ≤ b)
    (h : eLpNorm f 1 P ≤ ENNReal.ofReal b) : ∫ ω, f ω ∂P ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  calc
    ENNReal.ofReal (∫ ω, f ω ∂P) = ENNReal.ofReal (∫ ω, ‖f ω‖ ∂P) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hfn ω)).symm
    _ = eLpNorm f 1 P := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hf, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ENNReal.ofReal b := h

theorem uniform_square_tail
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hUI : UniformIntegrable (fun i ω => (X i ω) ^ 2) 1 P) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ i,
      (∫ ω in {ω | K < |X i ω|}, (X i ω) ^ 2 ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨C, hC⟩ := hUI.spec (by norm_num) (by norm_num) hε
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro i
  have hsq : Integrable (fun ω => (X i ω) ^ 2) P :=
    memLp_one_iff_integrable.mp (hUI.memLp i)
  let A : Set Ω := {ω | C ≤ ‖(X i ω) ^ 2‖₊}
  have hA : MeasurableSet A := measurableSet_le measurable_const ((hX i).pow_const 2).nnnorm
  have htail : (∫ ω, A.indicator (fun ω => (X i ω) ^ 2) ω ∂P) ≤ ε :=
    integral_nonneg_le_of_eLpNorm_one_le (hsq.indicator hA)
      (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω) hε.le (hC i)
  rw [integral_indicator hA] at htail
  refine (setIntegral_mono_set hsq.integrableOn
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) ?_).trans htail
  filter_upwards with ω hω
  change (C : ℝ) + 1 < |X i ω| at hω
  change C ≤ ‖(X i ω) ^ 2‖₊
  have hreal : (C : ℝ) ≤ ‖(X i ω) ^ 2‖ := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (X i ω), sq_nonneg (|X i ω| - 1), C.coe_nonneg]
  exact_mod_cast hreal

lemma integrable_cfRemainder_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (hX2 : Integrable (fun ω => (X ω) ^ 2) P) (u : ℝ) :
    Integrable (fun ω => cfRemainder (u * X ω)) P := by
  apply (hX2.const_mul (4 * u ^ 2)).mono' (by unfold cfRemainder; fun_prop)
  filter_upwards with ω
  simpa [mul_pow, mul_assoc] using norm_cfRemainder_le_square (u * X ω)

lemma integral_cfRemainder_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) P) (hmean : ∫ ω, X ω ∂P = 0) (u : ℝ) :
    (∫ ω, cfRemainder (u * X ω) ∂P) =
      (∫ ω, Complex.exp (((u * X ω : ℝ) : ℂ) * I) ∂P) - 1 +
        (u : ℂ) ^ 2 / 2 * (∫ ω, (X ω) ^ 2 ∂P : ℝ) := by
  have hXi : Integrable X P :=
    ((memLp_two_iff_integrable_sq hX.aestronglyMeasurable).2 hX2).integrable (by norm_num)
  have hexp : Integrable (fun ω => Complex.exp (((u * X ω : ℝ) : ℂ) * I)) P :=
    Integrable.of_bound (by fun_prop) 1
      (Filter.Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I (u * X ω)).le)
  have hlin : Integrable (fun ω => ((u * X ω : ℝ) : ℂ) * I) P :=
    (hXi.const_mul u).ofReal.mul_const I
  have hquad : Integrable (fun ω => (((u * X ω : ℝ) : ℂ) ^ 2 / 2)) P := by
    apply (hX2.const_mul (u ^ 2 / 2)).mono' (by fun_prop)
    filter_upwards with ω
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, sq_abs]
    rw [mul_pow]
    ring_nf
    exact le_rfl
  have hAdd := integral_add ((hexp.sub (integrable_const 1)).sub hlin) hquad
  have hSub := integral_sub (hexp.sub (integrable_const 1)) hlin
  have hSub' := integral_sub hexp (integrable_const (1 : ℂ))
  simp only [Pi.sub_apply] at hAdd hSub
  unfold cfRemainder
  rw [hAdd, hSub, hSub']
  have hlin0 : (∫ ω, ((u * X ω : ℝ) : ℂ) * I ∂P) = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hmean]
    simp
  have hquad_eq : (∫ ω, (((u * X ω : ℝ) : ℂ) ^ 2 / 2) ∂P) =
      (u : ℂ) ^ 2 / 2 * (∫ ω, (X ω) ^ 2 ∂P : ℝ) := by
    calc
      _ = ∫ ω, ((u : ℂ) ^ 2 / 2) * (((X ω) ^ 2 : ℝ) : ℂ) ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        push_cast
        ring
      _ = _ := by rw [integral_const_mul, integral_complex_ofReal]
  rw [hlin0, hquad_eq]
  simp

theorem uniform_cf_taylor
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hUI : UniformIntegrable (fun i ω => (X i ω) ^ 2) 1 P) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ i u, |u| < δ →
      ‖(∫ ω, Complex.exp (((u * X i ω : ℝ) : ℂ) * I) ∂P) - 1 +
        (u : ℂ) ^ 2 / 2 * (∫ ω, (X i ω) ^ 2 ∂P : ℝ)‖ ≤ η * u ^ 2 := by
  intro η hη
  have hsq : ∀ i, Integrable (fun ω => (X i ω) ^ 2) P :=
    fun i => memLp_one_iff_integrable.mp (hUI.memLp i)
  obtain ⟨M, hM⟩ := hUI.2.2
  have hmoment : ∀ i, (∫ ω, (X i ω) ^ 2 ∂P) ≤ (M : ℝ) := by
    intro i
    apply integral_nonneg_le_of_eLpNorm_one_le (hsq i) (fun _ => sq_nonneg _)
      M.coe_nonneg
    simpa using hM i
  obtain ⟨C, hC⟩ := hUI.spec (by norm_num) (by norm_num) (show 0 < η / 8 by positivity)
  let K : ℝ := (C : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min (1 / K) (η / (2 * K * ((M : ℝ) + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro i u hu
  let A : Set Ω := {ω | C ≤ ‖(X i ω) ^ 2‖₊}
  let g : Ω → ℝ := A.indicator (fun ω => (X i ω) ^ 2)
  have hA : MeasurableSet A := measurableSet_le measurable_const ((hX i).pow_const 2).nnnorm
  have hg : Integrable g P := (hsq i).indicator hA
  have hgn : ∀ ω, 0 ≤ g ω := by
    intro ω
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have htail : (∫ ω, g ω ∂P) ≤ η / 8 := by
    exact integral_nonneg_le_of_eLpNorm_one_le hg hgn (by positivity) (hC i)
  have huK : |u| * K ≤ 1 := by
    have hlt : |u| < 1 / K := hu.trans_le (min_le_left _ _)
    exact (lt_div_iff₀ hK).mp hlt |>.le
  have huM : |u| * K * (M : ℝ) ≤ η / 2 := by
    have hlt : |u| < η / (2 * K * ((M : ℝ) + 1)) :=
      hu.trans_le (min_le_right _ _)
    have hpos : 0 < 2 * K * ((M : ℝ) + 1) := by positivity
    have hmul := (lt_div_iff₀ hpos).mp hlt
    have hnonneg : 0 ≤ |u| * K := by positivity
    nlinarith
  have hpoint : ∀ ω, ‖cfRemainder (u * X i ω)‖ ≤
      u ^ 2 * (|u| * K * (X i ω) ^ 2 + 4 * g ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · have hgω : g ω = (X i ω) ^ 2 := Set.indicator_of_mem hω _
      rw [hgω]
      have h := norm_cfRemainder_le_square (u * X i ω)
      rw [mul_pow] at h
      have hpos : 0 ≤ u ^ 2 * (|u| * K * (X i ω) ^ 2) := by positivity
      nlinarith
    · have hgω : g ω = 0 := Set.indicator_of_notMem hω _
      rw [hgω, mul_zero, add_zero]
      have hsqC : (X i ω) ^ 2 < (C : ℝ) := by
        have hh : ‖(X i ω) ^ 2‖₊ < C := lt_of_not_ge hω
        have hh' : ‖(X i ω) ^ 2‖ < (C : ℝ) := by exact_mod_cast hh
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hh'
      have hxK : |X i ω| ≤ K := by
        dsimp [K]
        nlinarith [sq_abs (X i ω), abs_nonneg (X i ω), C.coe_nonneg]
      exact norm_cfRemainder_mul_le hK.le hxK huK
  rw [← integral_cfRemainder_mul (hX i) (hsq i) (hmean i)]
  calc
    ‖∫ ω, cfRemainder (u * X i ω) ∂P‖ ≤ ∫ ω, ‖cfRemainder (u * X i ω)‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, u ^ 2 * (|u| * K * (X i ω) ^ 2 + 4 * g ω) ∂P :=
      integral_mono (integrable_cfRemainder_mul (hX i) (hsq i) u).norm
        (((hsq i).const_mul (|u| * K)).add (hg.const_mul 4) |>.const_mul (u ^ 2)) hpoint
    _ = u ^ 2 * (|u| * K * (∫ ω, (X i ω) ^ 2 ∂P) + 4 * ∫ ω, g ω ∂P) := by
      rw [integral_const_mul, integral_add ((hsq i).const_mul _) (hg.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ u ^ 2 * (η / 2 + 4 * (η / 8)) := by
      gcongr
      exact (mul_le_mul_of_nonneg_left (hmoment i) (by positivity)).trans huM
    _ = η * u ^ 2 := by ring

end DenkerCLT

end DenkerComponent5

section DenkerComponent6

open MeasureTheory ProbabilityTheory MarkovChainCLT Complex
open scoped ENNReal ProbabilityTheory

namespace DenkerCLT

-- New complex algebra around the registered real covariance theorem 22845952.
-- No body from its accepted proof is copied or imported by a private helper name.
theorem alpha_cov_complex
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℂ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (M : ℝ) (hM : 0 ≤ M) (hUb : ∀ ω, ‖U ω‖ ≤ M) (hVb : ∀ ω, ‖V ω‖ ≤ M) :
    ‖(∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)‖ ≤
      16 * M ^ 2 * alphaMixingCoef P Y n := by
  have hUm : Measurable U := hU.mono (_root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  have hVm : Measurable V := hV.mono (_root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  have hUi : Integrable U P :=
    Integrable.of_bound hUm.aestronglyMeasurable M (Filter.Eventually.of_forall hUb)
  have hVi : Integrable V P :=
    Integrable.of_bound hVm.aestronglyMeasurable M (Filter.Eventually.of_forall hVb)
  have hUVi : Integrable (fun ω => U ω * V ω) P := by
    apply Integrable.of_bound (by fun_prop) (M ^ 2)
    filter_upwards with ω
    rw [norm_mul, pow_two]
    exact mul_le_mul (hUb ω) (hVb ω) (norm_nonneg _) hM
  have hUrb : ∀ ω, |(U ω).re| ≤ M := fun ω => (Complex.abs_re_le_norm _).trans (hUb ω)
  have hUib : ∀ ω, |(U ω).im| ≤ M := fun ω => (Complex.abs_im_le_norm _).trans (hUb ω)
  have hVrb : ∀ ω, |(V ω).re| ≤ M := fun ω => (Complex.abs_re_le_norm _).trans (hVb ω)
  have hVib : ∀ ω, |(V ω).im| ≤ M := fun ω => (Complex.abs_im_le_norm _).trans (hVb ω)
  have hUr : MemLp (fun ω => (U ω).re) 2 P :=
    MemLp.of_bound (by fun_prop) M (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hUrb)
  have hUi2 : MemLp (fun ω => (U ω).im) 2 P :=
    MemLp.of_bound (by fun_prop) M (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hUib)
  have hVr : MemLp (fun ω => (V ω).re) 2 P :=
    MemLp.of_bound (by fun_prop) M (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hVrb)
  have hVi2 : MemLp (fun ω => (V ω).im) 2 P :=
    MemLp.of_bound (by fun_prop) M (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hVib)
  have hrr := _root_.NumberCLTPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY n k (fun ω => (U ω).re) (fun ω => (V ω).re)
    (by fun_prop) (by fun_prop) M hM hUrb hVrb
  have hii := _root_.NumberCLTPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY n k (fun ω => (U ω).im) (fun ω => (V ω).im)
    (by fun_prop) (by fun_prop) M hM hUib hVib
  have hri := _root_.NumberCLTPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY n k (fun ω => (U ω).re) (fun ω => (V ω).im)
    (by fun_prop) (by fun_prop) M hM hUrb hVib
  have hir := _root_.NumberCLTPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY n k (fun ω => (U ω).im) (fun ω => (V ω).re)
    (by fun_prop) (by fun_prop) M hM hUib hVrb
  have hUre := integral_re (𝕜 := ℂ) hUi
  have hVre := integral_re (𝕜 := ℂ) hVi
  have hUim := integral_im (𝕜 := ℂ) hUi
  have hVim := integral_im (𝕜 := ℂ) hVi
  have hUVre := integral_re (𝕜 := ℂ) hUVi
  have hUVim := integral_im (𝕜 := ℂ) hUVi
  simp only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] at hUre hVre hUim hVim hUVre hUVim
  have hre : ((∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)).re =
      cov[fun ω => (U ω).re, fun ω => (V ω).re; P] -
        cov[fun ω => (U ω).im, fun ω => (V ω).im; P] := by
    rw [Complex.sub_re, Complex.mul_re, ← hUVre, ← hUre, ← hVre, ← hUim, ← hVim]
    simp only [Complex.mul_re]
    have hsplit := integral_sub (hUr.integrable_mul hVr) (hUi2.integrable_mul hVi2)
    simp only [Pi.mul_apply] at hsplit
    rw [hsplit, covariance_eq_sub hUr hVr, covariance_eq_sub hUi2 hVi2]
    simp only [Pi.mul_apply]
    ring
  have him : ((∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)).im =
      cov[fun ω => (U ω).re, fun ω => (V ω).im; P] +
        cov[fun ω => (U ω).im, fun ω => (V ω).re; P] := by
    rw [Complex.sub_im, Complex.mul_im, ← hUVim, ← hUre, ← hVre, ← hUim, ← hVim]
    simp only [Complex.mul_im]
    have hsplit := integral_add (hUr.integrable_mul hVi2) (hUi2.integrable_mul hVr)
    simp only [Pi.mul_apply] at hsplit
    rw [hsplit, covariance_eq_sub hUr hVi2, covariance_eq_sub hUi2 hVr]
    simp only [Pi.mul_apply]
    ring
  calc
    ‖(∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)‖ ≤
        |((∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)).re| +
        |((∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|cov[fun ω => (U ω).re, fun ω => (V ω).re; P]| +
          |cov[fun ω => (U ω).im, fun ω => (V ω).im; P]|) +
        (|cov[fun ω => (U ω).re, fun ω => (V ω).im; P]| +
          |cov[fun ω => (U ω).im, fun ω => (V ω).re; P]|) := by
      rw [hre, him]
      exact add_le_add (abs_sub _ _) (abs_add_le _ _)
    _ ≤ 16 * M ^ 2 * alphaMixingCoef P Y n := by linarith

lemma norm_prod_le_one {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) : ‖∏ i ∈ s, z i‖ ≤ 1 := by
  exact (Finset.norm_prod_le s z).trans
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) hz)

lemma norm_pow_sub_pow_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : a ^ (n + 1) - b ^ (n + 1) =
          (a ^ n - b ^ n) * a + b ^ n * (a - b) := by
        rw [pow_succ, pow_succ]
        ring
      rw [heq]
      calc
        ‖(a ^ n - b ^ n) * a + b ^ n * (a - b)‖ ≤
            ‖a ^ n - b ^ n‖ * ‖a‖ + ‖b ^ n‖ * ‖a - b‖ := by
          simpa only [norm_mul] using norm_add_le ((a ^ n - b ^ n) * a) (b ^ n * (a - b))
        _ ≤ ‖a ^ n - b ^ n‖ + ‖a - b‖ := by
          grw [ha, norm_pow, pow_le_one₀ (norm_nonneg b) hb]
          simp
        _ ≤ (n : ℝ) * ‖a - b‖ + ‖a - b‖ := add_le_add ih le_rfl
        _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

theorem norm_integral_prod_sub_prod_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (hZb : ∀ j ω, ‖Z j ω‖ ≤ 1) (a : ℝ)
    (hstep : ∀ m : ℕ,
      ‖(∫ ω, (∏ j ∈ Finset.range m, Z j ω) * Z m ω ∂P) -
        (∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) * (∫ ω, Z m ω ∂P)‖ ≤ a)
    (m : ℕ) :
    ‖(∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) -
      ∏ j ∈ Finset.range m, (∫ ω, Z j ω ∂P)‖ ≤ (m : ℝ) * a := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlast : ‖∫ ω, Z m ω ∂P‖ ≤ 1 := by
        simpa using norm_integral_le_of_norm_le_const (μ := P)
          (Filter.Eventually.of_forall (hZb m))
      simp only [Finset.prod_range_succ]
      have heq :
          (∫ ω, (∏ j ∈ Finset.range m, Z j ω) * Z m ω ∂P) -
              (∏ j ∈ Finset.range m, ∫ ω, Z j ω ∂P) * (∫ ω, Z m ω ∂P) =
          ((∫ ω, (∏ j ∈ Finset.range m, Z j ω) * Z m ω ∂P) -
              (∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) * (∫ ω, Z m ω ∂P)) +
          ((∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) -
              ∏ j ∈ Finset.range m, (∫ ω, Z j ω ∂P)) * (∫ ω, Z m ω ∂P) := by ring
      rw [heq]
      calc
        _ ≤
            ‖(∫ ω, (∏ j ∈ Finset.range m, Z j ω) * Z m ω ∂P) -
              (∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) * (∫ ω, Z m ω ∂P)‖ +
            ‖((∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) -
              ∏ j ∈ Finset.range m, (∫ ω, Z j ω ∂P)) * (∫ ω, Z m ω ∂P)‖ :=
          norm_add_le _ _
        _ ≤ a + ‖(∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) -
              ∏ j ∈ Finset.range m, (∫ ω, Z j ω ∂P)‖ := by
          apply add_le_add (hstep m)
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) hlast
        _ ≤ a + (m : ℝ) * a := add_le_add le_rfl ih
        _ = ((m + 1 : ℕ) : ℝ) * a := by push_cast; ring

theorem alpha_prod_factorization
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (gap : ℕ) (cut : ℕ → ℕ)
    (Z : ℕ → Ω → ℂ) (hZb : ∀ j ω, ‖Z j ω‖ ≤ 1)
    (hpast : ∀ m, 0 < m → Measurable[processSigma Y (Set.Iic (cut m))]
      (fun ω => ∏ j ∈ Finset.range m, Z j ω))
    (hfuture : ∀ m, 0 < m → Measurable[processSigma Y (Set.Ici (cut m + gap))] (Z m))
    (m : ℕ) :
    ‖(∫ ω, ∏ j ∈ Finset.range m, Z j ω ∂P) -
      ∏ j ∈ Finset.range m, (∫ ω, Z j ω ∂P)‖ ≤
      (m : ℝ) * (16 * alphaMixingCoef P Y gap) := by
  apply norm_integral_prod_sub_prod_integral_le P Z hZb (16 * alphaMixingCoef P Y gap)
  intro r
  by_cases hr : r = 0
  · subst r
    have ha : 0 ≤ alphaMixingCoef P Y gap := by
      simpa using _root_.NumberCLTPort_MarkovChainCLT_alpha_indicator_cov_le.solution P Y gap 0 ∅ ∅ (by simp) (by simp)
    simpa using mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) ha
  simpa using alpha_cov_complex P Y hY gap (cut r)
    (fun ω => ∏ j ∈ Finset.range r, Z j ω) (Z r)
    (hpast r (Nat.pos_of_ne_zero hr)) (hfuture r (Nat.pos_of_ne_zero hr)) 1
    (by norm_num) (fun ω => norm_prod_le_one _ _ (fun j _ => hZb j ω)) (hZb r)

end DenkerCLT

end DenkerComponent6

section DenkerComponent7

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

noncomputable def hardClip (M x : ℝ) : ℝ := if |x| ≤ M then x else 0

theorem hardClip_measurable (M : ℝ) : Measurable (hardClip M) := by
  exact Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
    measurable_id measurable_const

theorem abs_hardClip_le (M x : ℝ) : |hardClip M x| ≤ |x| := by
  by_cases h : |x| ≤ M
  · simp [hardClip, h]
  · simp [hardClip, h]

theorem abs_hardClip_bound {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |hardClip M x| ≤ M := by
  by_cases h : |x| ≤ M
  · simp [hardClip, h]
  · simpa [hardClip, h] using hM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem hardClip_memLp {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hL2 : MemLp U 2 P) (M : ℝ) :
    MemLp (fun ω => hardClip M (U ω)) 2 P := by
  apply hL2.of_le ((hardClip_measurable M).comp hU).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using abs_hardClip_le M (U ω))

theorem hardClip_error_secondNorm_sq {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hL2 : MemLp U 2 P) (M : ℝ) :
    secondNorm P (fun ω => U ω - hardClip M (U ω)) ^ 2 =
      ∫ ω in {ω | M < |U ω|}, U ω ^ 2 ∂P := by
  have hsq := secondNorm_sq (hL2.sub (hardClip_memLp hU hL2 M))
  change secondNorm P (fun ω => U ω - hardClip M (U ω)) ^ 2 =
    ∫ ω, (U ω - hardClip M (U ω)) ^ 2 ∂P at hsq
  rw [hsq]
  rw [← integral_indicator (measurableSet_lt measurable_const hU.abs)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases h : |U ω| ≤ M
    · simp [hardClip, h, not_lt.mpr h]
    · simp [hardClip, h, lt_of_not_ge h])

theorem hardClip_error_secondNorm_le {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hL2 : MemLp U 2 P) (M : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htail : ∫ ω in {ω | M < |U ω|}, U ω ^ 2 ∂P ≤ δ ^ 2) :
    secondNorm P (fun ω => U ω - hardClip M (U ω)) ≤ δ := by
  have hs := hardClip_error_secondNorm_sq hU hL2 M
  have hn := secondNorm_nonneg P (fun ω => U ω - hardClip M (U ω))
  nlinarith

theorem alpha_covariance_of_square_tails (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (q k : ℕ)
    (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + q))] V)
    (hUL2 : MemLp U 2 P) (hVL2 : MemLp V 2 P)
    (hUN : secondNorm P U ≤ 1) (hVN : secondNorm P V ≤ 1)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hUt : ∫ ω in {ω | M < |U ω|}, U ω ^ 2 ∂P ≤ δ ^ 2)
    (hVt : ∫ ω in {ω | M < |V ω|}, V ω ^ 2 ∂P ≤ δ ^ 2) :
    |cov[U, V; P]| ≤ 4 * M ^ 2 * alphaMixingCoef P Y q + 4 * δ := by
  have hUm : Measurable U := hU.mono (_root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  have hVm : Measurable V := hV.mono (_root_.NumberCLTPort_MarkovChainCLT_processSigma_le_of_measurable.solution Y hY _) le_rfl
  let Uc : Ω → ℝ := fun ω => hardClip M (U ω)
  let Vc : Ω → ℝ := fun ω => hardClip M (V ω)
  have hUc : MemLp Uc 2 P := hardClip_memLp hUm hUL2 M
  have hVc : MemLp Vc 2 P := hardClip_memLp hVm hVL2 M
  have hUcN : secondNorm P Uc ≤ 1 :=
    (secondNorm_mono hUc hUL2 (Filter.Eventually.of_forall
      (fun ω => abs_hardClip_le M (U ω)))).trans hUN
  have hRU : secondNorm P (fun ω => U ω - Uc ω) ≤ δ :=
    hardClip_error_secondNorm_le hUm hUL2 M hδ hUt
  have hRV : secondNorm P (fun ω => V ω - Vc ω) ≤ δ :=
    hardClip_error_secondNorm_le hVm hVL2 M hδ hVt
  have hclip := _root_.NumberCLTPort_MarkovChainCLT_alpha_cov_bounded.solution P Y hY q k Uc Vc
    ((hardClip_measurable M).comp hU) ((hardClip_measurable M).comp hV)
    M hM (fun ω => abs_hardClip_bound hM (U ω))
    (fun ω => abs_hardClip_bound hM (V ω))
  have hfirst : |cov[fun ω => U ω - Uc ω, V; P]| ≤ 2 * δ := by
    calc
      _ ≤ 2 * secondNorm P (fun ω => U ω - Uc ω) * secondNorm P V :=
        abs_covariance_le_two_secondNorm (hUL2.sub hUc) hVL2
      _ ≤ 2 * δ := by
        have h0 := secondNorm_nonneg P (fun ω => U ω - Uc ω)
        have h1 := secondNorm_nonneg P V
        nlinarith
  have hsecond : |cov[Uc, fun ω => V ω - Vc ω; P]| ≤ 2 * δ := by
    calc
      _ ≤ 2 * secondNorm P Uc * secondNorm P (fun ω => V ω - Vc ω) :=
        abs_covariance_le_two_secondNorm hUc (hVL2.sub hVc)
      _ ≤ 2 * δ := by
        have h0 := secondNorm_nonneg P Uc
        have h1 := secondNorm_nonneg P (fun ω => V ω - Vc ω)
        nlinarith
  have hid : cov[U, V; P] = cov[Uc, Vc; P] +
      cov[fun ω => U ω - Uc ω, V; P] +
      cov[Uc, fun ω => V ω - Vc ω; P] := by
    rw [covariance_fun_sub_left hUL2 hUc hVL2,
      covariance_fun_sub_right hUc hVL2 hVc]
    ring
  rw [hid]
  calc
    _ ≤ |cov[Uc, Vc; P]| + |cov[fun ω => U ω - Uc ω, V; P]| +
        |cov[Uc, fun ω => V ω - Vc ω; P]| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * M ^ 2 * alphaMixingCoef P Y q + 4 * δ := by linarith

end DenkerCLT

end DenkerComponent7

section DenkerComponent8

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable def normalizedBlock (P : Measure Ω) (Y : ℕ → Ω → ℝ) (a n : ℕ) : Ω → ℝ :=
  fun ω => blockSum Y a n ω / sigma P Y n

omit mΩ in
theorem blockSum_measurable_processSigma (Y : ℕ → Ω → ℝ) (a n : ℕ) (s : Set ℕ)
    (h : ∀ i < n, i + a ∈ s) : Measurable[processSigma Y s] (blockSum Y a n) := by
  apply Finset.measurable_sum
  intro i hi
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (i + a) (le_iSup_of_le (h i (Finset.mem_range.mp hi)) le_rfl)

theorem normalizedBlock_measurable (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (a n : ℕ) :
    Measurable (normalizedBlock P Y a n) :=
  (blockSum_measurable Y hY a n).div_const _

theorem normalizedBlock_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (a n : ℕ) : MemLp (normalizedBlock P Y a n) 2 P := by
  unfold normalizedBlock
  simpa only [div_eq_mul_inv] using
    (blockSum_memLp P Y hY hstat hL2 a n).mul_const (sigma P Y n)⁻¹

theorem normalizedBlock_integral (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (g : ℝ → ℝ) (hg : Measurable g) (a n : ℕ) :
    ∫ ω, g (normalizedBlock P Y a n ω) ∂P =
      ∫ ω, g (normalizedSum P Y n ω) ∂P :=
  stationary_block_integral P Y hY hstat (fun x => g (x / sigma P Y n))
    (hg.comp (measurable_id.div_const _)) a n

theorem normalizedBlock_secondNorm_le_one (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (a n : ℕ) : secondNorm P (normalizedBlock P Y a n) ≤ 1 := by
  have hs := secondNorm_sq (normalizedBlock_memLp P Y hY hstat hL2 a n)
  rw [normalizedBlock_integral P Y hY hstat (fun x => x ^ 2)
    (measurable_id.pow_const 2) a n] at hs
  have hb := normalizedSum_second_moment_le_one P Y n
  have hn := secondNorm_nonneg P (normalizedBlock P Y a n)
  nlinarith

theorem normalizedBlock_square_tail (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (M : ℝ) (a n : ℕ) :
    (∫ ω in {ω | M < |normalizedBlock P Y a n ω|}, normalizedBlock P Y a n ω ^ 2 ∂P) =
      ∫ ω in {ω | M < |normalizedSum P Y n ω|}, normalizedSum P Y n ω ^ 2 ∂P := by
  rw [← integral_indicator (measurableSet_lt measurable_const
      (normalizedBlock_measurable P Y hY a n).abs),
    ← integral_indicator (measurableSet_lt measurable_const
      (normalizedSum_measurable P Y hY n).abs)]
  have hg : Measurable (fun x : ℝ => if M < |x| then x ^ 2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      (measurable_id.pow_const 2) measurable_const
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    normalizedBlock_integral P Y hY hstat _ hg a n

theorem normalizedBlock_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P) (a n : ℕ) :
    ∫ ω, normalizedBlock P Y a n ω ∂P = 0 := by
  have h : (∫ ω, normalizedBlock P Y a n ω ∂P) =
      ∫ ω, normalizedSum P Y n ω ∂P :=
    normalizedBlock_integral P Y hY hstat id measurable_id a n
  exact h.trans (normalizedSum_integral_zero P Y hY hstat hcent hL2 n)

theorem uniform_normalizedBlock_covariance (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ q ≥ Q, ∀ a b m n cut : ℕ,
      (∀ i < m, i + a ≤ cut) → cut + q ≤ b →
      |cov[normalizedBlock P Y a m, normalizedBlock P Y b n; P]| ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM, htail⟩ := uniform_square_tail P (normalizedSum P Y)
    (normalizedSum_measurable P Y hY) hUI (δ ^ 2) (sq_pos_of_pos hδ)
  have ht : Tendsto (fun q => 4 * M ^ 2 * alphaMixingCoef P Y q) atTop (𝓝 0) := by
    simpa using hmix.const_mul (4 * M ^ 2)
  have he : ∀ᶠ q : ℕ in atTop, 4 * M ^ 2 * alphaMixingCoef P Y q < ε / 2 :=
    ht.eventually (gt_mem_nhds (by linarith))
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 he
  refine ⟨Q, ?_⟩
  intro q hq a b m n cut hpast hfuture
  have hu : Measurable[processSigma Y (Set.Iic cut)] (normalizedBlock P Y a m) :=
    (blockSum_measurable_processSigma Y a m _ hpast).div_const _
  have hv : Measurable[processSigma Y (Set.Ici (cut + q))] (normalizedBlock P Y b n) :=
    (blockSum_measurable_processSigma Y b n _ (fun i _ => by
      change cut + q ≤ i + b
      omega)).div_const _
  have h := alpha_covariance_of_square_tails P Y hY q cut
    (normalizedBlock P Y a m) (normalizedBlock P Y b n) hu hv
    (normalizedBlock_memLp P Y hY hstat hL2 a m)
    (normalizedBlock_memLp P Y hY hstat hL2 b n)
    (normalizedBlock_secondNorm_le_one P Y hY hstat hL2 a m)
    (normalizedBlock_secondNorm_le_one P Y hY hstat hL2 b n)
    M δ hM.le hδ.le
    (by rw [normalizedBlock_square_tail P Y hY hstat M a m]; exact htail m)
    (by rw [normalizedBlock_square_tail P Y hY hstat M b n]; exact htail n)
  have := hQ q hq
  dsimp [δ] at h
  linarith

end DenkerCLT

end DenkerComponent8

section DenkerComponent9

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem secondNorm_sum_sq_sub_card_le (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → ℝ) (k : ℕ) (hW : ∀ i < k, MemLp (W i) 2 P)
    (hmean : ∀ i < k, ∫ ω, W i ω ∂P = 0)
    (hsecond : ∀ i < k, ∫ ω, W i ω ^ 2 ∂P = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcross : ∀ i < k, ∀ j < k, i ≠ j → |cov[W i, W j; P]| ≤ ε) :
    |secondNorm P (fun ω => ∑ i ∈ Finset.range k, W i ω) ^ 2 - (k : ℝ)| ≤
      (k : ℝ) ^ 2 * ε := by
  have hsum : MemLp (fun ω => ∑ i ∈ Finset.range k, W i ω) 2 P :=
    memLp_finsetSum _ (fun i hi => hW i (Finset.mem_range.mp hi))
  have hsummean : (∫ ω, ∑ i ∈ Finset.range k, W i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i hi => (hW i (Finset.mem_range.mp hi)).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun i hi => hmean i (Finset.mem_range.mp hi))
  have hdiag : ∀ i < k, cov[W i, W i; P] = 1 := by
    intro i hi
    rw [covariance_eq_sub (hW i hi) (hW i hi), hmean i hi, zero_mul, sub_zero]
    simpa only [← sq, Pi.pow_apply] using hsecond i hi
  have hid : secondNorm P (fun ω => ∑ i ∈ Finset.range k, W i ω) ^ 2 =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, cov[W i, W j; P] := by
    rw [← covariance_fun_sum_fun_sum' (fun i hi => hW i (Finset.mem_range.mp hi))
      (fun i hi => hW i (Finset.mem_range.mp hi)), covariance_eq_sub hsum hsum,
      hsummean, zero_mul, sub_zero, secondNorm_sq hsum]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => sq _)
  have hbase : (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      if i = j then (1 : ℝ) else 0) = (k : ℝ) := by
    calc
      _ = ∑ i ∈ Finset.range k, (1 : ℝ) := Finset.sum_congr rfl
        (fun i hi => by simp [Finset.mem_range.mp hi])
      _ = (k : ℝ) := by simp
  have hdiff : secondNorm P (fun ω => ∑ i ∈ Finset.range k, W i ω) ^ 2 - (k : ℝ) =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        (cov[W i, W j; P] - if i = j then (1 : ℝ) else 0) := by
    simp only [Finset.sum_sub_distrib]
    rw [hid, hbase]
  rw [hdiff]
  calc
    _ ≤ ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        |cov[W i, W j; P] - if i = j then (1 : ℝ) else 0| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simpa [hdiag i (Finset.mem_range.mp hi)] using hε
      · simpa [hij] using hcross i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
    _ = (k : ℝ) ^ 2 * ε := by simp; ring

theorem separated_normalized_variance_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ q ≥ Q, ∀ k m : ℕ,
      variance P Y m ≠ 0 →
      |secondNorm P (fun ω => ∑ i ∈ Finset.range k,
        normalizedBlock P Y (i * (m + q)) m ω) ^ 2 - (k : ℝ)| ≤ (k : ℝ) ^ 2 * ε := by
  intro ε hε
  obtain ⟨Q, hQ⟩ := uniform_normalizedBlock_covariance P Y hY hstat hL2 hUI hmix ε hε
  refine ⟨Q, ?_⟩
  intro q hq k m hm
  apply secondNorm_sum_sq_sub_card_le P _ k
  · intro i _
    exact normalizedBlock_memLp P Y hY hstat hL2 _ _
  · intro i _
    exact normalizedBlock_integral_zero P Y hY hstat hcent hL2 _ _
  · intro i _
    rw [normalizedBlock_integral P Y hY hstat (fun x => x ^ 2)
      (measurable_id.pow_const 2), normalizedSum_second_moment, div_self hm]
  · exact hε.le
  · intro i hi j hj hij
    have hordered : ∀ a b : ℕ, a < b →
        |cov[normalizedBlock P Y (a * (m + q)) m,
          normalizedBlock P Y (b * (m + q)) m; P]| ≤ ε := by
      intro a b hab
      apply hQ q hq _ _ _ _ (a * (m + q) + m)
      · intro r hr
        omega
      · have hmul := Nat.mul_le_mul_right (m + q) (Nat.succ_le_of_lt hab)
        nlinarith
    rcases lt_or_gt_of_ne hij with h | h
    · exact hordered i j h
    · rw [covariance_comm]
      exact hordered j i h

end DenkerCLT

end DenkerComponent9

section DenkerComponent10

open Filter
open scoped Topology

namespace DenkerCLT

theorem tendsto_bounded_div_atTop_zero
    (f s : Nat -> Real) (hs : Tendsto s atTop atTop)
    (C : Real) (hf : forall n, |f n| <= C) :
    Tendsto (fun n => f n / s n) atTop (𝓝 0) := by
  have hC : Tendsto (fun n => C / s n) atTop (𝓝 (0 : Real)) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => C) atTop (𝓝 C)).mul
        (tendsto_inv_atTop_zero.comp hs)
  apply Metric.tendsto_nhds.2
  intro eps heps
  filter_upwards [hC.eventually (gt_mem_nhds heps),
    hs.eventually (eventually_gt_atTop (0 : Real))] with n hn hnpos
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos]
  exact (div_le_div_of_nonneg_right (hf n) hnpos.le).trans_lt hn

theorem abs_sub_le_of_sq_sub_sq_le
    {x r eps : Real} (hx : 0 <= x) (hr : 0 < r)
    (h : |x ^ 2 - r ^ 2| <= eps * r) : |x - r| <= eps := by
  have heq : |x ^ 2 - r ^ 2| = |x - r| * (x + r) := by
    rw [show x ^ 2 - r ^ 2 = (x - r) * (x + r) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hx hr.le)]
  apply (mul_le_mul_iff_left₀ hr).1
  calc
    |x - r| * r <= |x - r| * (x + r) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx) (abs_nonneg _)
    _ = |x ^ 2 - r ^ 2| := heq.symm
    _ <= eps * r := h

theorem variance_scaling_of_fixed_gap_comparison
    (s : Nat -> Real) (b : Nat -> Nat -> Real) (k : Nat) (hk : 0 < k)
    (hs : Tendsto s atTop atTop) (hb : forall q m, 0 <= b q m)
    (hcomparison : forall q, exists C : Real,
      forall m, |s (k * m) - b q m| <= C)
    (hsquare : forall eta : Real, 0 < eta -> exists q : Nat,
      ∀ᶠ m : Nat in atTop, |(b q m / s m) ^ 2 - (k : Real)| <= eta) :
    Tendsto (fun m => s (k * m) / s m) atTop (𝓝 (Real.sqrt (k : Real))) := by
  have hr : 0 < Real.sqrt (k : Real) := Real.sqrt_pos.2 (by exact_mod_cast hk)
  apply Metric.tendsto_nhds.2
  intro eps heps
  obtain ⟨q, hq⟩ := hsquare ((eps / 2) * Real.sqrt (k : Real))
    (mul_pos (half_pos heps) hr)
  obtain ⟨C, hC⟩ := hcomparison q
  have hd := tendsto_bounded_div_atTop_zero
    (fun m => s (k * m) - b q m) s hs C hC
  have hd' : ∀ᶠ m : Nat in atTop,
      |s (k * m) / s m - b q m / s m| < eps / 2 := by
    simpa only [Real.dist_eq, sub_zero, sub_div] using
      (Metric.tendsto_nhds.1 hd (eps / 2) (half_pos heps))
  filter_upwards [hq, hd', hs.eventually (eventually_gt_atTop (0 : Real))]
    with m hm hdm hsm
  have hclose : |b q m / s m - Real.sqrt (k : Real)| <= eps / 2 := by
    apply abs_sub_le_of_sq_sub_sq_le (div_nonneg (hb q m) hsm.le) hr
    simpa only [Real.sq_sqrt (Nat.cast_nonneg k)] using hm
  rw [Real.dist_eq]
  calc
    |s (k * m) / s m - Real.sqrt (k : Real)| <=
        |s (k * m) / s m - b q m / s m| +
          |b q m / s m - Real.sqrt (k : Real)| := abs_sub_le _ _ _
    _ < eps / 2 + eps / 2 := add_lt_add_of_lt_of_le hdm hclose
    _ = eps := add_halves eps

theorem tendsto_nat_floor_div_atTop (k : Nat) (hk : 0 < k) :
    Tendsto (fun n : Nat => n / k) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * k)] with n hn
  exact (Nat.le_div_iff_mul_le hk).2 hn

theorem inverse_floor_variance_scaling
    (s : Nat -> Real) (k : Nat) (hk : 0 < k) (hs : Tendsto s atTop atTop)
    (hinteger : Tendsto (fun m => s (k * m) / s m) atTop
      (𝓝 (Real.sqrt (k : Real))))
    (hcomparison : exists C : Real,
      forall n, |s n - s (k * (n / k))| <= C) :
    Tendsto (fun n => s (n / k) / s n) atTop
      (𝓝 (1 / Real.sqrt (k : Real))) := by
  have hfloor := tendsto_nat_floor_div_atTop k hk
  have hsFloor := hs.comp hfloor
  obtain ⟨C, hC⟩ := hcomparison
  have hd := tendsto_bounded_div_atTop_zero
    (fun n => s n - s (k * (n / k))) (fun n => s (n / k)) hsFloor C hC
  have hint := hinteger.comp hfloor
  have hratio : Tendsto (fun n => s n / s (n / k)) atTop
      (𝓝 (Real.sqrt (k : Real))) := by
    convert hint.add hd using 1
    · ext n
      change s n / s (n / k) = s (k * (n / k)) / s (n / k) +
        (s n - s (k * (n / k))) / s (n / k)
      ring
    · simp
  have hr : Real.sqrt (k : Real) ≠ 0 :=
    (Real.sqrt_pos.2 (show (0 : Real) < k by exact_mod_cast hk)).ne'
  simpa only [inv_div, one_div] using hratio.inv₀ hr

end DenkerCLT

end DenkerComponent10

section DenkerComponent11

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sigma_tendsto_atTop (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hvar : Tendsto (variance P Y) atTop atTop) :
    Tendsto (sigma P Y) atTop atTop := by
  apply tendsto_atTop.2
  intro r
  filter_upwards [hvar.eventually (eventually_ge_atTop (r ^ 2))] with n hn
  calc
    r ≤ |r| := le_abs_self r
    _ = Real.sqrt (r ^ 2) := (Real.sqrt_sq_eq_abs r).symm
    _ ≤ sigma P Y n := Real.sqrt_le_sqrt hn

theorem normalizedSeparated_secondNorm (P : Measure Ω) (Y : ℕ → Ω → ℝ) (k m q : ℕ) :
    secondNorm P (fun ω => ∑ i ∈ Finset.range k,
      normalizedBlock P Y (i * (m + q)) m ω) =
      secondNorm P (separatedSum Y k m q) / sigma P Y m := by
  rw [← abs_of_nonneg (sigma_nonneg P Y m), ← secondNorm_div_const]
  congr 1
  funext ω
  simp only [normalizedBlock, separatedSum, Finset.sum_div]

theorem stationary_integer_sigma_ratio (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0))
    (hvar : Tendsto (variance P Y) atTop atTop) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun m => sigma P Y (k * m) / sigma P Y m) atTop
      (𝓝 (Real.sqrt (k : ℝ))) := by
  apply variance_scaling_of_fixed_gap_comparison (sigma P Y)
    (fun q m => secondNorm P (separatedSum Y k m q)) k hk
    (sigma_tendsto_atTop P Y hvar) (fun q m => secondNorm_nonneg P _)
  · intro q
    refine ⟨2 * (k : ℝ) ^ 2 * (q : ℝ) * secondNorm P (Y 0), ?_⟩
    intro m
    have h := abs_secondNorm_sub_le
      (separatedSum_memLp P Y hY hstat hL2 k m q)
      (partialSum_memLp P Y hY hstat hL2 (k * m))
    rw [abs_sub_comm] at h
    exact h.trans (secondNorm_separatedSum_sub_partialSum_le P Y hY hstat hL2 k m q)
  · intro η hη
    let ε : ℝ := η / ((k : ℝ) ^ 2 + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨Q, hQ⟩ := separated_normalized_variance_bound P Y hY hstat hcent hL2 hUI hmix ε hε
    refine ⟨Q, ?_⟩
    filter_upwards [hvar.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
    have hb := hQ Q le_rfl k m (ne_of_gt hm)
    rw [normalizedSeparated_secondNorm] at hb
    apply hb.trans
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 2 + 1)).2
    nlinarith

theorem stationary_floor_sigma_ratio (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0))
    (hvar : Tendsto (variance P Y) atTop atTop) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => sigma P Y (n / k) / sigma P Y n) atTop
      (𝓝 (1 / Real.sqrt (k : ℝ))) := by
  apply inverse_floor_variance_scaling (sigma P Y) k hk (sigma_tendsto_atTop P Y hvar)
    (stationary_integer_sigma_ratio P Y hY hstat hcent hL2 hUI hmix hvar k hk)
  refine ⟨(k : ℝ) * secondNorm P (Y 0), ?_⟩
  intro n
  exact (abs_secondNorm_sub_le (partialSum_memLp P Y hY hstat hL2 n)
    (partialSum_memLp P Y hY hstat hL2 (k * (n / k)))).trans
    (secondNorm_partialSum_division_sub_le P Y hY hstat hL2 n k hk)

end DenkerCLT

end DenkerComponent11

section DenkerComponent12

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT Complex
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def fourierIntegral (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * I) ∂P

theorem fourier_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * I)) P := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun ω => (Complex.norm_exp_ofReal_mul_I (t * X ω)).le)

theorem norm_fourierIntegral_le_one (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (t : ℝ) : ‖fourierIntegral P X t‖ ≤ 1 := by
  simpa only [fourierIntegral, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := P)
      (Filter.Eventually.of_forall (fun ω => (show
        ‖Complex.exp (((t * X ω : ℝ) : ℂ) * I)‖ ≤ 1 from
          (Complex.norm_exp_ofReal_mul_I (t * X ω)).le)))

theorem norm_exp_real_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have hid : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul]
  simpa [mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

theorem fourierIntegral_difference_le (P : Measure Ω) [IsProbabilityMeasure P]
    {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hUL2 : MemLp U 2 P) (hVL2 : MemLp V 2 P) (t : ℝ) :
    ‖fourierIntegral P U t - fourierIntegral P V t‖ ≤
      |t| * secondNorm P (fun ω => U ω - V ω) := by
  rw [fourierIntegral, fourierIntegral,
    ← integral_sub (fourier_integrable P hU t) (fourier_integrable P hV t)]
  calc
    _ ≤ ∫ ω, ‖Complex.exp (((t * U ω : ℝ) : ℂ) * I) -
        Complex.exp (((t * V ω : ℝ) : ℂ) * I)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |U ω - V ω| ∂P := by
      apply integral_mono
      · exact ((fourier_integrable P hU t).sub (fourier_integrable P hV t)).norm
      · exact ((hUL2.sub hVL2).integrable (by norm_num)).abs.const_mul _
      · intro ω
        simpa only [← mul_sub, abs_mul] using norm_exp_real_sub_le (t * U ω) (t * V ω)
    _ = |t| * (∫ ω, |U ω - V ω| ∂P) := integral_const_mul _ _
    _ ≤ |t| * secondNorm P (fun ω => U ω - V ω) :=
      mul_le_mul_of_nonneg_left (integral_abs_le_secondNorm (hUL2.sub hVL2)) (abs_nonneg _)

theorem stationary_block_fourier (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (a m : ℕ) (t : ℝ) :
    fourierIntegral P (blockSum Y a m) t = fourierIntegral P (partialSum Y m) t := by
  let g : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * I)
  have hg : Measurable g := by fun_prop
  unfold fourierIntegral
  change (∫ ω, g (blockSum Y a m ω) ∂P) = ∫ ω, g (partialSum Y m ω) ∂P
  rw [← integral_map (blockSum_measurable Y hY a m).aemeasurable hg.aestronglyMeasurable,
    stationary_block_law P Y hY hstat a m,
    integral_map (partialSum_measurable Y hY m).aemeasurable hg.aestronglyMeasurable]

theorem separated_fourier_factorization (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (k m q : ℕ) (t : ℝ) :
    ‖fourierIntegral P (fun ω => ∑ j ∈ Finset.range k, blockSum Y (j * (m + q)) m ω) t -
      fourierIntegral P (partialSum Y m) t ^ k‖ ≤
      (k : ℝ) * (16 * alphaMixingCoef P Y q) := by
  let Z : ℕ → Ω → ℂ := fun j ω => Complex.exp
    (((t * blockSum Y (j * (m + q)) m ω : ℝ) : ℂ) * I)
  let cut : ℕ → ℕ := fun r => (r - 1) * (m + q) + m
  have hZb : ∀ j ω, ‖Z j ω‖ ≤ 1 := fun j ω =>
    (Complex.norm_exp_ofReal_mul_I (t * blockSum Y (j * (m + q)) m ω)).le
  have hpast : ∀ r, 0 < r → Measurable[processSigma Y (Set.Iic (cut r))]
      (fun ω => ∏ j ∈ Finset.range r, Z j ω) := by
    intro r hr
    apply Finset.measurable_prod
    intro j hj
    have hb : Measurable[processSigma Y (Set.Iic (cut r))]
        (blockSum Y (j * (m + q)) m) := by
      apply blockSum_measurable_processSigma
      intro i hi
      have hjr : j ≤ r - 1 := by have := Finset.mem_range.mp hj; omega
      have hh := Nat.mul_le_mul_right (m + q) hjr
      change i + j * (m + q) ≤ (r - 1) * (m + q) + m
      omega
    dsimp [Z]
    fun_prop
  have hfuture : ∀ r, 0 < r → Measurable[processSigma Y (Set.Ici (cut r + q))] (Z r) := by
    intro r hr
    have hb : Measurable[processSigma Y (Set.Ici (cut r + q))]
        (blockSum Y (r * (m + q)) m) := by
      apply blockSum_measurable_processSigma
      intro i _
      have hr' : r - 1 + 1 = r := by omega
      have hh : (r - 1) * (m + q) + m + q = r * (m + q) := by
        nlinarith
      change (r - 1) * (m + q) + m + q ≤ i + r * (m + q)
      omega
    dsimp [Z]
    fun_prop
  have h := alpha_prod_factorization P Y hY q cut Z hZb hpast hfuture k
  have hprod : ∀ ω, (∏ j ∈ Finset.range k, Z j ω) =
      Complex.exp (((t * ∑ j ∈ Finset.range k, blockSum Y (j * (m + q)) m ω : ℝ) : ℂ) * I) := by
    intro ω
    rw [← Complex.exp_sum]
    congr 1
    simp only [ofReal_mul, ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  have hint : ∀ j, (∫ ω, Z j ω ∂P) = fourierIntegral P (partialSum Y m) t := by
    intro j
    exact stationary_block_fourier P Y hY hstat _ _ _
  simpa only [hprod, hint, Finset.prod_const, Finset.card_range, fourierIntegral] using h

theorem fourierIntegral_normalized (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) :
    fourierIntegral P (normalizedSum P Y n) t =
      fourierIntegral P (partialSum Y n) (t / sigma P Y n) := by
  unfold fourierIntegral
  apply integral_congr_ae
  filter_upwards with ω
  congr 2
  apply congrArg (fun x : ℝ => (x : ℂ))
  simp only [normalizedSum]
  ring

theorem fourierIntegral_block_scaled (P : Measure Ω) (Y : ℕ → Ω → ℝ) (m n : ℕ)
    (hm : sigma P Y m ≠ 0) (t : ℝ) :
    fourierIntegral P (partialSum Y m) (t / sigma P Y n) =
      fourierIntegral P (normalizedSum P Y m) (t * (sigma P Y m / sigma P Y n)) := by
  unfold fourierIntegral
  apply integral_congr_ae
  filter_upwards with ω
  congr 2
  apply congrArg (fun x : ℝ => (x : ℂ))
  simp only [normalizedSum]
  simp only [div_eq_mul_inv]
  calc
    t * (sigma P Y n)⁻¹ * partialSum Y m ω =
        (sigma P Y m * (sigma P Y m)⁻¹) *
          (t * (sigma P Y n)⁻¹ * partialSum Y m ω) := by rw [mul_inv_cancel₀ hm, one_mul]
    _ = t * (sigma P Y m * (sigma P Y n)⁻¹) *
        (partialSum Y m ω * (sigma P Y m)⁻¹) := by ring

end DenkerCLT

end DenkerComponent12

section DenkerComponent13

open MeasureTheory Filter Complex
open scoped ENNReal Topology

namespace DenkerCLT

noncomputable def cfQuadratic (u : ℝ) : ℂ := 1 - (u : ℂ) ^ 2 / 2

lemma norm_cfQuadratic_le {u : ℝ} (hu : |u| ≤ 1) : ‖cfQuadratic u‖ ≤ 1 := by
  have heq : cfQuadratic u = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
    simp [cfQuadratic]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hsq : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
  constructor <;> nlinarith [sq_nonneg u]

lemma gaussian_binomial_tendsto (t : ℝ) :
    Tendsto (fun k : ℕ => (cfQuadratic (t / Real.sqrt (k : ℝ))) ^ k) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have heq (k : ℕ) : cfQuadratic (t / Real.sqrt (k : ℝ)) =
      1 + (-(t : ℂ) ^ 2 / 2) / (k : ℂ) := by
    have hs : ((Real.sqrt (k : ℝ) : ℝ) : ℂ) ^ 2 = (k : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg k)
    unfold cfQuadratic
    rw [Complex.ofReal_div, div_pow, hs]
    ring
  simpa only [heq] using Complex.tendsto_one_add_div_pow_exp (-(t : ℂ) ^ 2 / 2)

theorem uniform_cf_power_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hUI : UniformIntegrable (fun i ω => (X i ω) ^ 2) 1 P)
    (hsecond : ∀ᶠ i : ℕ in atTop, ∫ ω, (X i ω) ^ 2 ∂P = 1)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
      ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝 (t / Real.sqrt (k : ℝ))) →
      ∀ᶠ n : ℕ in atTop,
        ‖(∫ ω, Complex.exp (((u n * X (m n) ω : ℝ) : ℂ) * I) ∂P) ^ k -
          Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε := by
  let η : ℝ := ε / (3 * (t ^ 2 + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, htaylor⟩ := uniform_cf_taylor P X hX hmean hUI η hη
  let d : ℝ := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hz : Tendsto (fun k : ℕ => t / Real.sqrt (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ k : ℕ in atTop, |t / Real.sqrt (k : ℝ)| < d := by
    exact (by simpa using hz.abs : Tendsto (fun k : ℕ => |t / Real.sqrt (k : ℝ)|)
      atTop (𝓝 (0 : ℝ))).eventually_lt_const hd
  have hgauss : Tendsto
      (fun k : ℕ => ‖cfQuadratic (t / Real.sqrt (k : ℝ)) ^ k -
        Complex.exp (-(t : ℂ) ^ 2 / 2)‖) atTop (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp (gaussian_binomial_tendsto t)
  have hgauss' := hgauss.eventually_lt_const (show 0 < ε / 3 by positivity)
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp hsmall
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp hgauss'
  refine ⟨max (max K₁ K₂) 1, le_max_right _ _, ?_⟩
  intro k hk m hm u hu
  have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hk₁ : K₁ ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hk₂ : K₂ ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have husmall : ∀ᶠ n : ℕ in atTop, |u n| < d := hu.abs.eventually_lt_const (hK₁ k hk₁)
  have hsec : ∀ᶠ n : ℕ in atTop, ∫ ω, (X (m n) ω) ^ 2 ∂P = 1 := hm.eventually hsecond
  have hscale : (k : ℝ) * (t / Real.sqrt (k : ℝ)) ^ 2 = t ^ 2 := by
    rw [div_pow, Real.sq_sqrt hkpos.le]
    field_simp [ne_of_gt hkpos]
  have hscale_lim : Tendsto (fun n : ℕ => (k : ℝ) * (u n) ^ 2) atTop (𝓝 (t ^ 2)) := by
    simpa only [hscale] using (hu.pow 2).const_mul (k : ℝ)
  have hscale_bound := hscale_lim.eventually_le_const (show t ^ 2 < t ^ 2 + 1 by linarith)
  have hpoly : Tendsto (fun n : ℕ => cfQuadratic (u n) ^ k) atTop
      (𝓝 (cfQuadratic (t / Real.sqrt (k : ℝ)) ^ k)) := by
    exact ((show Continuous (fun x : ℝ => cfQuadratic x ^ k) by
      unfold cfQuadratic
      fun_prop).tendsto _).comp hu
  have hpoly_norm : Tendsto
      (fun n : ℕ => ‖cfQuadratic (u n) ^ k - cfQuadratic (t / Real.sqrt (k : ℝ)) ^ k‖)
      atTop (𝓝 0) := by
    simpa using (hpoly.sub_const (cfQuadratic (t / Real.sqrt (k : ℝ)) ^ k)).norm
  have hpoly_bound := hpoly_norm.eventually_lt_const (show 0 < ε / 3 by positivity)
  filter_upwards [husmall, hsec, hscale_bound, hpoly_bound] with n hn hsn hscale_n hpoly_n
  let a : ℂ := ∫ ω, Complex.exp (((u n * X (m n) ω : ℝ) : ℂ) * I) ∂P
  have ha : ‖a‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := P)
        (Filter.Eventually.of_forall fun ω =>
          (Complex.norm_exp_ofReal_mul_I (u n * X (m n) ω)).le)
  have hu1 : |u n| ≤ 1 := hn.le.trans (min_le_right _ _)
  have hb : ‖cfQuadratic (u n)‖ ≤ 1 := norm_cfQuadratic_le hu1
  have herr : ‖a - cfQuadratic (u n)‖ ≤ η * (u n) ^ 2 := by
    have h := htaylor (m n) (u n) (hn.trans_le (min_le_left _ _))
    rw [hsn] at h
    have heq : a - cfQuadratic (u n) = a - 1 +
        (u n : ℂ) ^ 2 / 2 * ((1 : ℝ) : ℂ) := by
      unfold cfQuadratic
      push_cast
      ring
    rw [heq]
    exact h
  have hpow : ‖a ^ k - cfQuadratic (u n) ^ k‖ ≤ ε / 3 := by
    calc
      ‖a ^ k - cfQuadratic (u n) ^ k‖ ≤ (k : ℝ) * ‖a - cfQuadratic (u n)‖ :=
        norm_pow_sub_pow_le a (cfQuadratic (u n)) ha hb k
      _ ≤ (k : ℝ) * (η * (u n) ^ 2) := mul_le_mul_of_nonneg_left herr hkpos.le
      _ = η * ((k : ℝ) * (u n) ^ 2) := by ring
      _ ≤ η * (t ^ 2 + 1) := mul_le_mul_of_nonneg_left hscale_n hη.le
      _ = ε / 3 := by
        dsimp [η]
        field_simp [ne_of_gt (show (0 : ℝ) < t ^ 2 + 1 by positivity)]
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (a ^ k) (cfQuadratic (u n) ^ k)
    (Complex.exp (-(t : ℂ) ^ 2 / 2))
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub (cfQuadratic (u n) ^ k)
    (cfQuadratic (t / Real.sqrt (k : ℝ)) ^ k) (Complex.exp (-(t : ℂ) ^ 2 / 2))
  have hlast := hK₂ k hk₂
  change ‖a ^ k - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε
  linarith

end DenkerCLT

end DenkerComponent13

section DenkerComponent14

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT Complex
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem fourier_separated_error_tendsto_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (hvar : Tendsto (variance P Y) atTop atTop)
    (k q : ℕ) (hk : 0 < k) (t : ℝ) :
    Tendsto (fun n => ‖fourierIntegral P (normalizedSum P Y n) t -
      fourierIntegral P (separatedSum Y k (n / k) q) (t / sigma P Y n)‖)
      atTop (𝓝 0) := by
  let C : ℝ := (2 * (k : ℝ) ^ 2 * (q : ℝ) + (k : ℝ)) * secondNorm P (Y 0)
  have hbound : ∀ n, ‖fourierIntegral P (normalizedSum P Y n) t -
      fourierIntegral P (separatedSum Y k (n / k) q) (t / sigma P Y n)‖ ≤
        (|t| * C) / sigma P Y n := by
    intro n
    rw [fourierIntegral_normalized, norm_sub_rev]
    have hS : Measurable (separatedSum Y k (n / k) q) :=
      Finset.measurable_sum _ (fun j _ => blockSum_measurable Y hY _ _)
    calc
      _ ≤ |t / sigma P Y n| * secondNorm P (fun ω =>
          separatedSum Y k (n / k) q ω - partialSum Y n ω) :=
        fourierIntegral_difference_le P hS (partialSum_measurable Y hY n)
          (separatedSum_memLp P Y hY hstat hL2 k (n / k) q)
          (partialSum_memLp P Y hY hstat hL2 n) _
      _ ≤ |t / sigma P Y n| * C := mul_le_mul_of_nonneg_left
        (secondNorm_separatedSum_sub_partialSum_div_le P Y hY hstat hL2 n k q hk)
        (abs_nonneg _)
      _ = (|t| * C) / sigma P Y n := by
        rw [abs_div, abs_of_nonneg (sigma_nonneg P Y n)]
        ring
  have hlim : Tendsto (fun n => (|t| * C) / sigma P Y n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (sigma_tendsto_atTop P Y hvar)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
    (hbound n).trans_lt hn

theorem normalized_characteristic_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0))
    (hvar : Tendsto (variance P Y) atTop atTop) (t : ℝ) :
    Tendsto (fun n => fourierIntegral P (normalizedSum P Y n) t) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hsecond : ∀ᶠ m : ℕ in atTop, ∫ ω, normalizedSum P Y m ω ^ 2 ∂P = 1 := by
    filter_upwards [hvar.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
    rw [normalizedSum_second_moment, div_self (ne_of_gt hm)]
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨k, hk1, hpower⟩ := uniform_cf_power_approximation P (normalizedSum P Y)
    (normalizedSum_measurable P Y hY)
    (normalizedSum_integral_zero P Y hY hstat hcent hL2) hUI hsecond
    t (ε / 3) (by positivity)
  have hk : 0 < k := by omega
  have hu : Tendsto (fun n => t * (sigma P Y (n / k) / sigma P Y n)) atTop
      (𝓝 (t / Real.sqrt (k : ℝ))) := by
    simpa only [mul_one_div] using
      (stationary_floor_sigma_ratio P Y hY hstat hcent hL2 hUI hmix hvar k hk).const_mul t
  have hp := hpower k le_rfl (fun n => n / k) (tendsto_nat_floor_div_atTop k hk)
    (fun n => t * (sigma P Y (n / k) / sigma P Y n)) hu
  have hmix' : Tendsto (fun q => (k : ℝ) * (16 * alphaMixingCoef P Y q)) atTop (𝓝 0) := by
    simpa using (hmix.const_mul 16).const_mul (k : ℝ)
  obtain ⟨q, hq⟩ := (hmix'.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  have he := (fourier_separated_error_tendsto_zero P Y hY hstat hL2 hvar k q hk t).eventually
    (gt_mem_nhds (by positivity : 0 < ε / 3))
  have hnonzero : ∀ᶠ n : ℕ in atTop, sigma P Y (n / k) ≠ 0 := by
    filter_upwards [((sigma_tendsto_atTop P Y hvar).comp
      (tendsto_nat_floor_div_atTop k hk)).eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact ne_of_gt hn
  filter_upwards [hp, he, hnonzero] with n hpn hen hnn
  have hf := separated_fourier_factorization P Y hY hstat k (n / k) q (t / sigma P Y n)
  rw [fourierIntegral_block_scaled P Y (n / k) n hnn t] at hf
  change ‖fourierIntegral P (separatedSum Y k (n / k) q) (t / sigma P Y n) -
    fourierIntegral P (normalizedSum P Y (n / k))
      (t * (sigma P Y (n / k) / sigma P Y n)) ^ k‖ ≤ _ at hf
  change ‖fourierIntegral P (normalizedSum P Y (n / k))
    (t * (sigma P Y (n / k) / sigma P Y n)) ^ k -
      Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε / 3 at hpn
  rw [dist_eq_norm]
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (fourierIntegral P (normalizedSum P Y n) t)
    (fourierIntegral P (separatedSum Y k (n / k) q) (t / sigma P Y n))
    (Complex.exp (-(t : ℂ) ^ 2 / 2))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (fourierIntegral P (separatedSum Y k (n / k) q) (t / sigma P Y n))
    (fourierIntegral P (normalizedSum P Y (n / k))
      (t * (sigma P Y (n / k) / sigma P Y n)) ^ k)
    (Complex.exp (-(t : ℂ) ^ 2 / 2))
  linarith

end DenkerCLT

end DenkerComponent14

section DenkerComponent15

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT Complex
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem normalized_clt_of_uniformIntegrable (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hUI : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P)
    (hmix : Tendsto (fun q => alphaMixingCoef P Y q) atTop (𝓝 0))
    (hvar : Tendsto (variance P Y) atTop atTop) :
    TendstoInDistribution (normalizedSum P Y) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 1) := by
  refine ⟨fun n => (normalizedSum_measurable P Y hY n).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n => charFun (P.map (normalizedSum P Y n)) t) atTop
    (𝓝 (charFun ((gaussianReal 0 1).map id) t))
  have hchar (n : ℕ) : charFun (P.map (normalizedSum P Y n)) t =
      fourierIntegral P (normalizedSum P Y n) t := by
    rw [charFun_apply_real, integral_map
      (normalizedSum_measurable P Y hY n).aemeasurable (by fun_prop)]
    simp only [fourierIntegral, Complex.ofReal_mul]
  simp only [hchar, Measure.map_id, charFun_gaussianReal]
  simpa [neg_div] using normalized_characteristic_tendsto P Y hY hstat hcent hL2 hUI hmix hvar t

end DenkerCLT

end DenkerComponent15

section DenkerComponent16

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DenkerCLT

theorem uniform_small_of_antitone_cutoffs
    (a : Nat -> Nat -> Real) (b : Nat -> Real)
    (ha : forall n, Antitone (a n))
    (hrow : forall n, Tendsto (a n) atTop (𝓝 0))
    (hcol : forall k, Tendsto (fun n => a n k) atTop (𝓝 (b k)))
    (hb : Tendsto b atTop (𝓝 0)) :
    forall eps : Real, 0 < eps -> exists k, forall n, a n k <= eps := by
  intro eps heps
  obtain ⟨k, hk⟩ := (hb.eventually (gt_mem_nhds heps)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hcol k).eventually (gt_mem_nhds hk))
  have hfinite : ∀ᶠ j : Nat in atTop, forall i : Fin N, a i j < eps := by
    rw [Filter.eventually_all]
    intro i
    exact (hrow i).eventually (gt_mem_nhds heps)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hfinite
  refine ⟨max k K, fun n => ?_⟩
  by_cases hn : n < N
  · exact (ha n (le_max_right k K)).trans (hK K le_rfl ⟨n, hn⟩).le
  · exact (ha n (le_max_left k K)).trans (hN n (Nat.le_of_not_gt hn)).le

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  [IsProbabilityMeasure P]

theorem integrable_min_sq_const {f : Omega -> Real} (hf : MemLp f 2 P) (C : Real) :
    Integrable (fun x => min (f x ^ 2) C) P :=
  hf.integrable_sq.inf (integrable_const C)

theorem tendsto_integral_sq_min_residual {f : Omega -> Real} (hf : MemLp f 2 P) :
    Tendsto (fun k : Nat => ∫ x, f x ^ 2 - min (f x ^ 2) (k : Real) ∂P)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun (k : Nat) x => f x ^ 2 - min (f x ^ 2) (k : Real))
    (f := fun _ => (0 : Real)) (fun x => f x ^ 2)
    (fun k => (hf.aestronglyMeasurable.pow 2).sub
      (integrable_min_sq_const hf k).aestronglyMeasurable)
    hf.integrable_sq
    (fun k => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (min_le_left _ _))]
      exact sub_le_self _ (le_min (sq_nonneg _) (Nat.cast_nonneg _)))
    (ae_of_all _ fun x => by
      obtain ⟨K, hK⟩ := exists_nat_ge (f x ^ 2)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop K] with k hk
      have hle : f x ^ 2 <= (k : Real) := hK.trans (by exact_mod_cast hk)
      simp [min_eq_left hle])
  simpa using h

theorem integral_sq_min_residual_antitone {f : Omega -> Real} (hf : MemLp f 2 P) :
    Antitone (fun k : Nat => ∫ x, f x ^ 2 - min (f x ^ 2) (k : Real) ∂P) := by
  intro i j hij
  apply integral_mono (hf.integrable_sq.sub (integrable_min_sq_const hf j))
    (hf.integrable_sq.sub (integrable_min_sq_const hf i))
  intro x
  exact sub_le_sub_left (min_le_min_left _ (show (i : Real) <= (j : Real) from
    Nat.cast_le.mpr hij)) _

theorem tendsto_integral_clipped_square
    {Omega' : Type*} [MeasurableSpace Omega'] {Q : Measure Omega'}
    [IsProbabilityMeasure Q] {X : Nat -> Omega -> Real} {Z : Omega' -> Real}
    (hX : forall n, Measurable (X n)) (hZ : Measurable Z)
    (hdist : TendstoInDistribution X atTop Z (fun _ => P) Q) (k : Nat) :
    Tendsto (fun n => ∫ x, min (X n x ^ 2) (k : Real) ∂P) atTop
      (𝓝 (∫ x, min (Z x ^ 2) (k : Real) ∂Q)) := by
  let F : BoundedContinuousFunction Real Real := BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (x ^ 2) (k : Real), by fun_prop⟩ k (by
      intro x y
      rw [Real.dist_eq]
      change |min (x ^ 2) (k : Real) - min (y ^ 2) (k : Real)| <= (k : Real)
      apply abs_le.2
      constructor
      · have hx := le_min (sq_nonneg x) (Nat.cast_nonneg k : (0 : Real) <= k)
        have hy := min_le_right (y ^ 2) (k : Real)
        linarith
      · have hy := le_min (sq_nonneg y) (Nat.cast_nonneg k : (0 : Real) <= k)
        have hx := min_le_right (x ^ 2) (k : Real)
        linarith)
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hdist.tendsto F
  change Tendsto (fun n => ∫ x, F x ∂P.map (X n)) atTop
    (𝓝 (∫ x, F x ∂Q.map Z)) at h
  simp_rw [integral_map_of_stronglyMeasurable (hX _) F.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable hZ F.continuous.stronglyMeasurable] at h
  exact h

theorem eLpNorm_square_tail_le_residual
    {f : Omega -> Real} (hf : Measurable f) (hL2 : MemLp f 2 P) (k : Nat) :
    eLpNorm ({x | (2 * (k : NNReal)) <= ‖f x ^ 2‖₊}.indicator (fun x => f x ^ 2)) 1 P <=
      ENNReal.ofReal (2 * (∫ x, f x ^ 2 - min (f x ^ 2) (k : Real) ∂P)) := by
  let s : Set Omega := {x | (2 * (k : NNReal)) <= ‖f x ^ 2‖₊}
  have hs : MeasurableSet s := by
    apply measurableSet_le measurable_const
    exact (hf.pow_const 2).nnnorm
  have hi := hL2.integrable_sq.indicator hs
  have hr := hL2.integrable_sq.sub (integrable_min_sq_const hL2 k)
  change eLpNorm (s.indicator (fun x => f x ^ 2)) 1 P <= _
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ x, ‖s.indicator (fun x => f x ^ 2) x‖ ∂P) <=
        ∫ x, 2 * (f x ^ 2 - min (f x ^ 2) (k : Real)) ∂P := by
      apply integral_mono hi.norm (hr.const_mul 2)
      intro x
      change ‖s.indicator (fun x => f x ^ 2) x‖ <=
        2 * (f x ^ 2 - min (f x ^ 2) (k : Real))
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hxNN : (2 * (k : NNReal)) <= ‖f x ^ 2‖₊ := hx
        have hx' : ((2 * (k : NNReal)) : Real) <= ‖f x ^ 2‖ := NNReal.coe_le_coe.mpr hxNN
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hx'
        have hm := min_le_right (f x ^ 2) (k : Real)
        norm_num only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast] at hx'
        linarith
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact mul_nonneg (by norm_num) (sub_nonneg.2 (min_le_left _ _))
    _ = 2 * (∫ x, f x ^ 2 - min (f x ^ 2) (k : Real) ∂P) :=
      integral_const_mul _ _

theorem uniformIntegrable_sq_of_uniform_residual
    {X : Nat -> Omega -> Real} (hX : forall n, Measurable (X n))
    (hL2 : forall n, MemLp (X n) 2 P)
    (hres : forall eps : Real, 0 < eps -> exists k : Nat,
      forall n, (∫ x, X n x ^ 2 - min (X n x ^ 2) (k : Real) ∂P) <= eps) :
    UniformIntegrable (fun n x => X n x ^ 2) 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num)
    (fun n => (hL2 n).aestronglyMeasurable.pow 2)
  intro eps heps
  obtain ⟨k, hk⟩ := hres (eps / 2) (half_pos heps)
  refine ⟨2 * (k : NNReal), fun n => ?_⟩
  exact (eLpNorm_square_tail_le_residual (hX n) (hL2 n) k).trans
    (ENNReal.ofReal_le_ofReal (by linarith [hk n]))

theorem uniformIntegrable_sq_of_tendstoInDistribution
    {Omega' : Type*} [MeasurableSpace Omega'] {Q : Measure Omega'}
    [IsProbabilityMeasure Q] {X : Nat -> Omega -> Real} {Z : Omega' -> Real}
    (hX : forall n, Measurable (X n)) (hZ : Measurable Z)
    (hL2 : forall n, MemLp (X n) 2 P) (hZL2 : MemLp Z 2 Q)
    (hdist : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hmom : Tendsto (fun n => ∫ x, X n x ^ 2 ∂P) atTop
      (𝓝 (∫ x, Z x ^ 2 ∂Q))) :
    UniformIntegrable (fun n x => X n x ^ 2) 1 P := by
  apply uniformIntegrable_sq_of_uniform_residual hX hL2
  apply uniform_small_of_antitone_cutoffs
    (fun n k => ∫ x, X n x ^ 2 - min (X n x ^ 2) (k : Real) ∂P)
    (fun k => ∫ x, Z x ^ 2 - min (Z x ^ 2) (k : Real) ∂Q)
    (fun n => integral_sq_min_residual_antitone (hL2 n))
    (fun n => tendsto_integral_sq_min_residual (hL2 n))
    (fun k => ?_) (tendsto_integral_sq_min_residual hZL2)
  have h := hmom.sub (tendsto_integral_clipped_square hX hZ hdist k)
  simpa only [integral_sub (hL2 _).integrable_sq (integrable_min_sq_const (hL2 _) k),
    integral_sub hZL2.integrable_sq (integrable_min_sq_const hZL2 k)] using h

end DenkerCLT

end DenkerComponent16

section DenkerComponent17

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace DenkerCLT

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  [IsProbabilityMeasure P]

theorem integral_sq_standard_gaussian :
    (∫ x : Real, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := (0 : Real)) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem uniformIntegrable_normalized_squares_of_clt
    {S : Nat -> Omega -> Real} (hS : forall n, Measurable (S n))
    (hL2 : forall n, MemLp (S n) 2 P)
    (hvar : Tendsto (fun n => ∫ x, S n x ^ 2 ∂P) atTop atTop)
    (hdist : TendstoInDistribution
      (fun n x => S n x / Real.sqrt (∫ y, S n y ^ 2 ∂P)) atTop
      (id : Real -> Real) (fun _ => P) (gaussianReal 0 1)) :
    UniformIntegrable (fun n x => S n x ^ 2 / (∫ y, S n y ^ 2 ∂P)) 1 P := by
  let V : Nat -> Real := fun n => ∫ x, S n x ^ 2 ∂P
  have hV : forall n, 0 <= V n := fun n => integral_nonneg (fun x => sq_nonneg _)
  have hn : forall n, MemLp (fun x => S n x / Real.sqrt (V n)) 2 P := by
    intro n
    simpa only [div_eq_mul_inv] using (hL2 n).mul_const ((Real.sqrt (V n))⁻¹)
  have hmom : Tendsto (fun n => ∫ x, (S n x / Real.sqrt (V n)) ^ 2 ∂P)
      atTop (𝓝 (1 : Real)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hvar.eventually (eventually_gt_atTop (0 : Real))] with n hnpos
    have hnpos' : 0 < V n := hnpos
    simp_rw [div_pow, Real.sq_sqrt (hV n)]
    rw [integral_div, div_self hnpos'.ne']
  have hui := uniformIntegrable_sq_of_tendstoInDistribution
    (fun n => (hS n).div_const _) measurable_id hn
    (memLp_id_gaussianReal' 2 (by norm_num)) hdist
    (by simpa only [id_eq, integral_sq_standard_gaussian] using hmom)
  apply hui.ae_eq
  intro n
  exact ae_of_all _ fun x => by simp [V, div_pow, Real.sq_sqrt (hV n)]

end DenkerCLT

end DenkerComponent17

section DenkerComponent18

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT DenkerCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hmix : Tendsto (fun n => alphaMixingCoef P Y n) atTop (𝓝 0))
    (hvar : Tendsto (fun n =>
      ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop atTop) :
    TendstoInDistribution
        (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω)
          / Real.sqrt (∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P))
        atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1)
      ↔ UniformIntegrable
          (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
            / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by
  constructor
  · intro hclt
    exact uniformIntegrable_normalized_squares_of_clt
      (partialSum_measurable Y hY) (partialSum_memLp P Y hY hstat hL2) hvar hclt
  · intro hUI
    have hUI' : UniformIntegrable (fun n ω => normalizedSum P Y n ω ^ 2) 1 P := by
      simpa only [normalizedSum_sq, partialSum, DenkerCLT.variance] using hUI
    exact normalized_clt_of_uniformIntegrable P Y hY hstat hcent hL2 hUI' hmix hvar

end DenkerComponent18


end OwnCandidate
#print axioms solution