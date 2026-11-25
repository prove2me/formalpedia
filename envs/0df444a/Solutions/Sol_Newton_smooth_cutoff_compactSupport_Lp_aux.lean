-- Prove2me | solution 1 for Newton.smooth_cutoff_compactSupport_Lp_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:18.729686+00:00
-- url     : https://prove2.me/submissions/d958fd4e-8240-4881-8f19-3e1bf7c8e66c

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Theorems.Thm_Newton_tsupport_subset_closedBall

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞) (hp_one : 1 ≤ p)
    (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g)
    (hg_compact : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      MemLp ψ p volume ∧
      eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by
  have _ := hp_one
  obtain ⟨Rg, hRg_subset, hRg_one⟩ := tsupport_subset_closedBall g hg_compact
  have hRg_pos : 0 < Rg := lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hRg_one
  set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (Rg + 1) with hS_def
  have hS_meas : MeasurableSet S :=
    (Metric.isClosed_closedBall :
      IsClosed (Metric.closedBall (0 : Fin n → ℝ) (Rg + 1))).measurableSet
  have hμS_lt_top : volume S < (⊤ : ℝ≥0∞) := by
    simpa [hS_def]
      using MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := Rg + 1)
  have hμS_ne_top : volume S ≠ (⊤ : ℝ≥0∞) := ne_of_lt hμS_lt_top
  let volFactor : ℝ≥0∞ := (volume S) ^ (1 / p.toReal)
  have hvol_ne_top : volFactor ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hμS_ne_top
    have hp_toReal_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    exact (div_nonneg zero_le_one hp_toReal_nonneg)
  let C : ℝ := volFactor.toReal
  have hC_nonneg : 0 ≤ C := ENNReal.toReal_nonneg
  set δ : ℝ := (ε / 8) / (C + 1) with hδ_def
  have hδ_pos : 0 < δ := by
    have hnum_pos : 0 < ε / 8 := by
      have : (0 : ℝ) < 8 := by norm_num
      exact div_pos hε this
    have hden_pos : 0 < C + 1 := add_pos_of_nonneg_of_pos hC_nonneg zero_lt_one
    simpa [hδ_def] using div_pos hnum_pos hden_pos
  have hg_uc : UniformContinuous g := hg_compact.uniformContinuous_of_continuous hg_cont
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_close⟩ := hg_uc.exists_contDiff_dist_le hδ_pos
  let fχ : ContDiffBump (0 : Fin n → ℝ) := ⟨Rg, Rg + 1, hRg_pos, by simp⟩
  let χ : (Fin n → ℝ) → ℝ := fχ
  have hχ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) χ := fχ.contDiff
  have hχ_support : HasCompactSupport χ := fχ.hasCompactSupport
  have hχ_one : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) Rg, χ x = (1 : ℝ) := by
    intro x hx
    simpa [χ] using fχ.one_of_mem_closedBall hx
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x; simpa [χ] using fχ.nonneg' x
  have hχ_le_one : ∀ x, χ x ≤ 1 := by
    intro x
    simpa [χ] using (fχ.le_one (x := x))
  set ψ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ₀ x with hψ_def
  have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ :=
    hχ_smooth.smul hφ₀_smooth
  have hψ_support : HasCompactSupport ψ :=
    (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_memLp : MemLp ψ p volume :=
    hψ_cont.memLp_of_hasCompactSupport hψ_support
  have hg_zero_outside_ball :
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∉ Metric.closedBall (0 : Fin n → ℝ) Rg → g x = 0 := by
    intro x hx
    have hx_not_support : x ∉ tsupport g := by
      intro hx_support
      exact hx (hRg_subset hx_support)
    simpa using image_eq_zero_of_notMem_tsupport hx_not_support
  have hχ_zero_outside : ∀ {x : Fin n → ℝ}, x ∉ S → χ x = 0 := by
    intro x hxS
    have hx_not_ball : x ∉ Metric.ball (0 : Fin n → ℝ) (Rg + 1) := by
      intro hx_ball
      exact hxS (Metric.ball_subset_closedBall hx_ball)
    have hx_not_support : x ∉ Function.support χ := by
      simpa [χ, fχ.support_eq] using hx_not_ball
    simpa [Function.support] using hx_not_support
  set diff : (Fin n → ℝ) → ℂ := fun x => g x - ψ x with hdiff_def
  have hdiff_zero_outside : ∀ {x : Fin n → ℝ}, x ∉ S → diff x = 0 := by
    intro x hxS
    have hx_norm_gt : Rg + 1 < ‖x‖ := by
      have hx_not_le : ¬ ‖x‖ ≤ Rg + 1 := by simpa [S, hS_def, dist_eq_norm] using hxS
      exact lt_of_not_ge hx_not_le
    have hx_not_closed : x ∉ Metric.closedBall (0 : Fin n → ℝ) Rg := by
      intro hx_mem
      have hx_le : ‖x‖ ≤ Rg := by simpa [dist_eq_norm] using hx_mem
      have hx_gt : Rg < ‖x‖ := lt_of_le_of_lt (show (Rg : ℝ) ≤ Rg + 1 by linarith) hx_norm_gt
      exact (not_lt_of_ge hx_le) hx_gt
    have hxg_zero : g x = 0 := hg_zero_outside_ball hx_not_closed
    have hxχ_zero : χ x = 0 := hχ_zero_outside hxS
    simp [diff, ψ, hxg_zero, hxχ_zero]
  have h_pointwise : ∀ x ∈ S, ‖diff x‖ ≤ δ := by
    intro x hxS
    have hx_norm_le : dist x (0 : Fin n → ℝ) ≤ Rg + 1 := by
      simpa [S, hS_def, dist_eq_norm] using hxS
    have hx_mem_outer : x ∈ Metric.closedBall (0 : Fin n → ℝ) (Rg + 1) := by
      simpa [Metric.mem_closedBall, dist_eq_norm]
        using hx_norm_le
    by_cases hx_inner : x ∈ Metric.closedBall (0 : Fin n → ℝ) Rg
    · have hχx : χ x = (1 : ℝ) := hχ_one x hx_inner
      have hx_bound := hφ₀_close x
      have hx_lt : ‖φ₀ x - g x‖ < δ := by
        simpa [dist_eq_norm] using hx_bound
      have hx_norm : ‖φ₀ x - g x‖ ≤ δ := le_of_lt hx_lt
      simpa [diff, ψ, hχx, norm_sub_rev]
        using hx_norm
    · have hxg_zero : g x = 0 := hg_zero_outside_ball hx_inner
      have hxφ₀_lt : ‖φ₀ x‖ < δ := by
        have hx_bound := hφ₀_close x
        simpa [dist_eq_norm, hxg_zero, norm_sub_rev] using hx_bound
      have hxφ₀_le : ‖φ₀ x‖ ≤ δ := le_of_lt hxφ₀_lt
      have hχ_norm_le : ‖χ x‖ ≤ 1 := by
        have hx_le := hχ_le_one x
        have hx_nonneg := hχ_nonneg x
        have hx_abs : |χ x| = χ x := abs_of_nonneg hx_nonneg
        have hx_norm : ‖χ x‖ = χ x := by simp [Real.norm_eq_abs, hx_abs]
        simpa [hx_norm]
          using hx_le
      have hxψ_le : ‖ψ x‖ ≤ δ := by
        have hxψ_norm : ‖ψ x‖ = ‖χ x‖ * ‖φ₀ x‖ := by
          simp [ψ]
        have hx_mul_le : ‖χ x‖ * ‖φ₀ x‖ ≤ ‖φ₀ x‖ :=
          (mul_le_of_le_one_left (norm_nonneg _) hχ_norm_le)
        have hψ_le_phi : ‖ψ x‖ ≤ ‖φ₀ x‖ := by
          simpa [ψ, norm_smul] using hx_mul_le
        exact hψ_le_phi.trans hxφ₀_le
      simpa [diff, hxg_zero]
        using hxψ_le
  have h_pointwise_all : ∀ x, ‖diff x‖ ≤ δ := by
    intro x
    by_cases hxS : x ∈ S
    · exact h_pointwise x hxS
    · have hx_zero : diff x = 0 := hdiff_zero_outside hxS
      simp [hx_zero, le_of_lt hδ_pos]
  have h_ae_bound :
      ∀ᵐ x ∂volume.restrict S, ‖diff x‖ ≤ δ :=
    Filter.Eventually.of_forall h_pointwise_all
  have h_indicator_eq : Set.indicator S diff = diff := by
    funext x
    by_cases hxS : x ∈ S
    · simp [diff, hxS]
    · have hx_zero : diff x = 0 := hdiff_zero_outside hxS
      simp [Set.indicator, hxS, diff, hx_zero]
  have h_eLp_eq :
      eLpNorm diff p volume = eLpNorm diff p (volume.restrict S) := by
    have h_indicator :=
      (eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (p := p) (s := S) (f := diff) hS_meas)
    simpa [h_indicator_eq] using h_indicator
  have h_eLp_le_aux :
      eLpNorm diff p (volume.restrict S)
        ≤ volFactor * ENNReal.ofReal δ := by
    have h_aux :=
      (eLpNorm_le_of_ae_bound
        (μ := volume.restrict S) (p := p) (f := diff) h_ae_bound)
    have h_simplified :
        eLpNorm diff p (volume.restrict S)
          ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
      simpa [Measure.restrict_apply, hS_meas, hS_def]
        using h_aux
    simpa [volFactor] using h_simplified
  have h_eLp_le :
      eLpNorm diff p volume ≤ volFactor * ENNReal.ofReal δ := by
    simpa [h_eLp_eq] using h_eLp_le_aux
  have h_volfactor_eq : volFactor = ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hvol_ne_top).symm
  have h_vol_le : volFactor ≤ ENNReal.ofReal (C + 1) := by
    have hC_le : C ≤ C + 1 := by linarith
    simpa [h_volfactor_eq] using ENNReal.ofReal_le_ofReal hC_le
  have h_mul_le :
      volFactor * ENNReal.ofReal δ
        ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal δ :=
    mul_le_mul_left h_vol_le _
  have h_mul_eq :
      ENNReal.ofReal (C + 1) * ENNReal.ofReal δ
        = ENNReal.ofReal (ε / 8) := by
    have hden_pos : 0 < C + 1 := add_pos_of_nonneg_of_pos hC_nonneg zero_lt_one
    have hden_ne_zero : C + 1 ≠ 0 := ne_of_gt hden_pos
    have hden_nonneg : 0 ≤ C + 1 := le_of_lt hden_pos
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have h_mul :
        ENNReal.ofReal (C + 1) * ENNReal.ofReal δ
          = ENNReal.ofReal ((C + 1) * δ) :=
      (ENNReal.ofReal_mul hden_nonneg).symm
    have h_cancel : (C + 1) * δ = ε / 8 := by
      simp [δ, div_eq_mul_inv, hden_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    simp [h_mul, h_cancel]
  have h_eLp_le' : eLpNorm diff p volume ≤ ENNReal.ofReal (ε / 8) :=
    h_eLp_le.trans <| h_mul_le.trans <| le_of_eq h_mul_eq
  have hε_eighth_lt : ε / 8 < ε / 4 := by
    have : (1 : ℝ) / 8 < 1 / 4 := by norm_num
    have hε_pos : 0 < ε := hε
    have := mul_lt_mul_of_pos_left this hε_pos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  have h_eLp_lt : eLpNorm diff p volume < ENNReal.ofReal (ε / 4) :=
    lt_of_le_of_lt h_eLp_le'
      ((ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2 hε_eighth_lt)
  refine ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, ?_⟩
  have hε_quarter_lt_real : ε / 4 < ε := by
    have : (0 : ℝ) < ε := hε
    linarith
  have hε_quarter_lt : ENNReal.ofReal (ε / 4) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 hε_quarter_lt_real
  exact lt_trans h_eLp_lt hε_quarter_lt
end Newton
