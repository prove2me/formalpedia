-- Prove2me | solution 1 for NechitaRDM.MP.dilation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:01:07.098898+00:00
-- url     : https://prove2.me/submissions/9e445ef9-426d-4685-9592-10890455e740

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

open MeasureTheory Filter Topology

theorem solution (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∃ K : Set ℝ, IsCompact K ∧ ν Kᶜ = 0)
    (hμ : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 1)) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂((μ n).map fun x => t n * x)) atTop
        (𝓝 (∫ x, f x ∂ν)) := by
  intro f
  obtain ⟨K, hK, hνK⟩ := hν
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R0 0 with hR
  have hR0' : 0 ≤ R := le_max_right _ _
  have hKR : ∀ x ∈ K, |x| ≤ R := by
    intro x hx
    have := hR0 hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact this.trans (le_max_left _ _)
  -- cutoff function
  let φ0 : C(ℝ, ℝ) := ⟨fun x => min 1 (max 0 (|x| - R)), by fun_prop⟩
  let φ : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound φ0 1 (by
    intro x y
    simp only [φ0, ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]
    constructor <;>
    · have := min_le_left 1 (max 0 (|x| - R)); have := min_le_left 1 (max 0 (|y| - R))
      have := le_min zero_le_one (le_max_left 0 (|x| - R))
      have := le_min zero_le_one (le_max_left 0 (|y| - R))
      linarith)
  have φapp : ∀ x, φ x = min 1 (max 0 (|x| - R)) := fun x => rfl
  have φnn : ∀ x, 0 ≤ φ x := fun x => by rw [φapp]; exact le_min zero_le_one (le_max_left _ _)
  have φone : ∀ x, R + 1 ≤ |x| → φ x = 1 := by
    intro x hx; rw [φapp]; apply min_eq_left; rw [max_eq_right (by linarith)]; linarith
  have hφν : ∫ x, φ x ∂ν = 0 := by
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ x ∂ν, x ∈ K := by
      rw [ae_iff]; simpa [Set.compl_def] using hνK
    filter_upwards [hae] with x hx
    rw [φapp, Pi.zero_apply, max_eq_left (by linarith [hKR x hx]), min_eq_right zero_le_one]
  have hφ := hμ φ
  rw [hφν] at hφ
  -- masses
  have hone := hμ (BoundedContinuousFunction.const ℝ 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    probReal_univ] at hone
  have hfin : ∀ᶠ n in atTop, IsFiniteMeasure (μ n) := by
    filter_upwards [hone.eventually (lt_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))] with n hn
    refine ⟨?_⟩
    by_contra h
    rw [not_lt, top_le_iff] at h
    simp [Measure.real, h] at hn
    linarith
  -- main difference
  let g : ℕ → BoundedContinuousFunction ℝ ℝ := fun n =>
    f.compContinuous ⟨fun x => t n * x, by fun_prop⟩
  have gapp : ∀ n x, g n x = f (t n * x) := fun n x => rfl
  have hmap : ∀ n, ∫ x, f x ∂((μ n).map fun x => t n * x) = ∫ x, g n x ∂(μ n) := by
    intro n
    rw [integral_map (measurable_const_mul (t n)).aemeasurable f.continuous.aestronglyMeasurable]; rfl
  simp only [hmap]
  have hdiff : Tendsto (fun n => ∫ x, g n x ∂(μ n) - ∫ x, f x ∂(μ n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := 2 * ‖f‖ + 1 with hC
    have hCpos : 0 < C := by positivity
    -- uniform continuity on a compact interval
    have huc : UniformContinuousOn f (Set.Icc (-(2 * (R + 1))) (2 * (R + 1))) :=
      isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 4) (by positivity)
    have htclose : ∀ᶠ n in atTop, |t n - 1| < min 1 (δ / (R + 2)) := by
      have := (Metric.tendsto_nhds.mp ht) (min 1 (δ / (R + 2))) (by positivity)
      filter_upwards [this] with n hn
      rwa [Real.dist_eq] at hn
    have hmass : ∀ᶠ n in atTop, (μ n).real Set.univ < 2 := hone.eventually (gt_mem_nhds (by norm_num))
    have hφsmall : ∀ᶠ n in atTop, ∫ x, φ x ∂(μ n) < ε / (2 * C) :=
      hφ.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hfin, htclose, hmass, hφsmall] with n hn htn hmn hφn
    rw [Real.dist_eq, sub_zero]
    have hpt : ∀ x, |g n x - f x| ≤ ε / 4 + C * φ x := by
      intro x
      rw [gapp]
      have ht1 : |t n - 1| < 1 := lt_of_lt_of_le htn (min_le_left _ _)
      have ht2 : |t n - 1| < δ / (R + 2) := lt_of_lt_of_le htn (min_le_right _ _)
      by_cases hx : |x| ≤ R + 1
      · have htabs : |t n| ≤ 2 := by
          have := abs_sub_abs_le_abs_sub (t n) 1; rw [abs_one] at this; linarith
        have hmem1 : t n * x ∈ Set.Icc (-(2 * (R + 1))) (2 * (R + 1)) := by
          rw [Set.mem_Icc, ← abs_le, abs_mul]
          exact mul_le_mul htabs hx (abs_nonneg _) (by norm_num)
        have hmem2 : x ∈ Set.Icc (-(2 * (R + 1))) (2 * (R + 1)) := by
          rw [Set.mem_Icc, ← abs_le]; linarith
        have hd : dist (t n * x) x < δ := by
          rw [Real.dist_eq, show t n * x - x = (t n - 1) * x by ring, abs_mul]
          calc |t n - 1| * |x| ≤ |t n - 1| * (R + 1) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
            _ ≤ (δ / (R + 2)) * (R + 1) := mul_le_mul_of_nonneg_right ht2.le (by linarith)
            _ < δ := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
        have := hδf _ hmem1 _ hmem2 hd
        rw [Real.dist_eq] at this
        have := mul_nonneg hCpos.le (φnn x)
        linarith
      · push_neg at hx
        rw [φone x hx.le, mul_one]
        have h1 := f.norm_coe_le_norm (t n * x)
        have h2 := f.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at h1 h2
        have := abs_sub (f (t n * x)) (f x)
        rw [hC]; linarith
    have hgi : Integrable (fun x => g n x) (μ n) := (g n).integrable _
    have hfi : Integrable (fun x => f x) (μ n) := f.integrable _
    have hφi : Integrable (fun x => φ x) (μ n) := φ.integrable _
    rw [← integral_sub hgi hfi]
    calc |∫ x, (g n x - f x) ∂(μ n)| ≤ ∫ x, |g n x - f x| ∂(μ n) := abs_integral_le_integral_abs
      _ ≤ ∫ x, (ε / 4 + C * φ x) ∂(μ n) := by
          apply integral_mono (hgi.sub hfi).abs ((integrable_const _).add (hφi.const_mul C)) hpt
      _ = ε / 4 * (μ n).real Set.univ + C * ∫ x, φ x ∂(μ n) := by
          rw [integral_add (integrable_const _) (hφi.const_mul C), integral_const, integral_const_mul,
            smul_eq_mul, mul_comm]
      _ < ε := by
          have hm0 : 0 ≤ (μ n).real Set.univ := measureReal_nonneg
          have : C * ∫ x, φ x ∂(μ n) < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hφn hCpos
          rw [show C * (ε / (2 * C)) = ε / 2 by field_simp] at this
          nlinarith
  have := hdiff.add (hμ f)
  rw [zero_add] at this
  refine this.congr (fun n => ?_)
  ring
