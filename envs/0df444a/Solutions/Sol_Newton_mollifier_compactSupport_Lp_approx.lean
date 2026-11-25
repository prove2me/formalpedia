-- Prove2me | solution 1 for Newton.mollifier_compactSupport_Lp_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:38.677778+00:00
-- url     : https://prove2.me/submissions/9893e2a6-bc96-4d3b-96cc-842c20086cc9

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
import Theorems.Thm_Newton_eLpNorm_triangle_ineq_lt
import Theorems.Thm_Newton_phi0_eq_zero_outside_enlarged_ball
section
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
namespace Newton
variable {n : ℕ}
private lemma continuous_compactSupport_memLp
    {ψ : (Fin n → ℝ) → ℂ}
    (hψ_cont : Continuous ψ)
    (hψ_support : HasCompactSupport ψ)
    (p : ℝ≥0∞) :
    MemLp ψ p (volume : Measure (Fin n → ℝ)) :=
  hψ_cont.memLp_of_hasCompactSupport (μ := volume) (p := p) hψ_support
end Newton
end

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g) (hg_compact : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) φ ∧
      eLpNorm (fun x => g x - φ x) p volume < ENNReal.ofReal ε ∧
      MemLp φ p volume := by
  have hg_uc : UniformContinuous g := hg_compact.uniformContinuous_of_continuous hg_cont
  -- The support is compact and has finite measure
  have hsupp_compact : IsCompact (tsupport g) := hg_compact
  have hsupp_finite : volume (tsupport g) < (∞ : ℝ≥0∞) := hsupp_compact.measure_lt_top
  -- Choose ε' such that pointwise approximation gives Lp bound
  -- We need to handle the case where the support has zero measure separately
  by_cases h_zero : volume (tsupport g) = 0
  · -- If support has measure zero, g = 0 a.e., so we can take φ = 0
    refine ⟨0, contDiff_const, ?_, MemLp.zero⟩
    have h_nonzero_subset : {x : (Fin n → ℝ) | g x ≠ 0} ⊆ tsupport g := by
      intro x hx
      by_contra hx'
      have hx_zero : g x = 0 := image_eq_zero_of_notMem_tsupport hx'
      exact hx hx_zero
    have h_nonzero_null : volume {x : (Fin n → ℝ) | g x ≠ 0} = 0 :=
      measure_mono_null h_nonzero_subset h_zero
    have hg_zero : g =ᵐ[volume] (0 : (Fin n → ℝ) → ℂ) := by
      have : ∀ᵐ x ∂volume, g x = 0 :=
        (ae_iff).2 (by simpa [Classical.not_not] using h_nonzero_null)
      exact this
    have hnorm_g : eLpNorm g p volume = 0 := by
      calc
        eLpNorm g p volume
            = eLpNorm (0 : (Fin n → ℝ) → ℂ) p volume :=
              (eLpNorm_congr_ae (μ := volume) hg_zero)
        _ = 0 := eLpNorm_zero
    have hnorm_g' : eLpNorm (fun x => g x) p volume = 0 := by
      simpa using hnorm_g
    have h_pos : 0 < ENNReal.ofReal ε := by
      simpa [ENNReal.ofReal_pos] using hε
    simpa [hnorm_g'] using h_pos
  · -- Choose a bounded region covering the support and set up quantitative bounds.
    have h_tsupport_compact : IsCompact (tsupport g) := hsupp_compact
    obtain ⟨R, hR_subset, hR_ge_one⟩ := tsupport_subset_closedBall g hg_compact
    set B : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R with hB_def
    have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
    have hB_meas : MeasurableSet B := by
      simpa [hB_def] using (Metric.isClosed_closedBall :
        IsClosed (Metric.closedBall (0 : Fin n → ℝ) R)).measurableSet
    have hμB_lt_top : volume B < ⊤ := by
      simpa [hB_def] using
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R))
    have hμB_ne_top : volume B ≠ ⊤ := ne_of_lt hμB_lt_top
    have hg_zero_outside : ∀ x ∉ B, g x = 0 := by
      intro x hxB
      by_contra hx_nonzero
      have hx_support : x ∈ Function.support g := by
        have : g x ≠ 0 := hx_nonzero
        simpa [Function.support] using this
      have hx_tsupport : x ∈ tsupport g := by
        have hx_closure : x ∈ closure (Function.support g) := subset_closure hx_support
        simpa [tsupport] using hx_closure
      exact hxB (hR_subset hx_tsupport)
    set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (R + 1) with hS_def
    have hS_meas : MeasurableSet S := by
      simpa [hS_def] using
        (Metric.isClosed_closedBall :
          IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + 1))).measurableSet
    have hμS_lt_top : volume S < ⊤ := by
      simpa [hS_def] using
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R + 1))
    have hμS_ne_top : volume S ≠ ⊤ := ne_of_lt hμS_lt_top
    have h_exponent_nonneg : 0 ≤ 1 / p.toReal := by
      have hp_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      exact (div_nonneg zero_le_one hp_nonneg)
    have h_pow_ne_top : (volume B) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
      ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμB_ne_top
    have h_powS_ne_top : (volume S) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
      ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμS_ne_top
    let denom : ℝ := max 1 ((volume S) ^ (1 / p.toReal)).toReal
    have hB_subset_S : B ⊆ S := by
      intro x hx
      have hx_norm_le : ‖x‖ ≤ R := by
        simpa [B, hB_def, dist_eq_norm] using Metric.mem_closedBall.mp hx
      have hx_norm_le' : ‖x‖ ≤ R + 1 := le_trans hx_norm_le (by linarith)
      exact Metric.mem_closedBall.mpr
        (by simpa [S, hS_def, dist_eq_norm] using hx_norm_le')
    have hμB_le_S : volume B ≤ volume S :=
      measure_mono hB_subset_S
    have hdenom_pos : 0 < denom := by
      have : (1 : ℝ) ≤ denom := le_max_left _ _
      exact lt_of_lt_of_le zero_lt_one this
    have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
    have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
    have hε_half : 0 < ε / 2 := half_pos hε
    have hε_denom_pos : 0 < ε / (8 * denom) := by
      have h_mul_pos : 0 < (8 : ℝ) * denom := mul_pos (by norm_num) hdenom_pos
      exact div_pos hε h_mul_pos
    have hε_denom_nonneg : 0 ≤ ε / (8 * denom) := le_of_lt hε_denom_pos
    set δ : ℝ := min (ε / 2) (ε / (8 * denom)) with hδ_def
    have hδ_pos : 0 < δ := by
      have hpos₁ : 0 < ε / 2 := hε_half
      have hpos₂ : 0 < ε / (8 * denom) := hε_denom_pos
      have hmin : 0 < min (ε / 2) (ε / (8 * denom)) := lt_min hpos₁ hpos₂
      simpa [δ, hδ_def] using hmin
    have h_powS_toReal_le : ((volume S) ^ (1 / p.toReal)).toReal ≤ denom := by
      simp [denom]
    obtain ⟨φ_raw, hφ_raw_smooth, hφ_raw_close⟩ :=
      hg_uc.exists_contDiff_dist_le hδ_pos
    -- Build a smooth cutoff `χ` which equals `1` on the ball covering the support
    -- and vanishes outside a slightly larger ball. This ensures compact support after cutting.
    let fχ : ContDiffBump (0 : Fin n → ℝ) := ⟨R, R + 1, hR_pos, by simp⟩
    let χ : (Fin n → ℝ) → ℝ := fχ
    have hχ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) χ := fχ.contDiff
    have hχ_support : HasCompactSupport χ := fχ.hasCompactSupport
    have hχ_one : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) R, χ x = (1 : ℝ) := by
      intro x hx
      simpa [χ] using fχ.one_of_mem_closedBall hx
    have hχ_nonneg : ∀ x, 0 ≤ χ x := by
      intro x
      simpa [χ] using fχ.nonneg' x
    have hχ_le_one : ∀ x, χ x ≤ 1 := by
      intro x
      simpa [χ] using (ContDiffBump.le_one (f := fχ) (x := x))
    set φ₀ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ_raw x with hφ₀_def
    have hφ₀_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ₀ :=
      hχ_smooth.smul hφ_raw_smooth
    have hφ₀_support : HasCompactSupport φ₀ :=
      (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
    have hφ₀_support_subset_supportχ :
        Function.support φ₀ ⊆ Function.support χ := by
      intro x hx
      have hxχ : χ x ≠ 0 := by
        have hxφ : φ₀ x ≠ 0 := hx
        by_contra hxχ
        have : φ₀ x = 0 := by simp [φ₀, hxχ]
        exact hxφ this
      simpa [Function.support] using hxχ
    have hφ₀_support_subset : Function.support φ₀ ⊆ Metric.ball (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_supportχ : x ∈ Function.support χ :=
        hφ₀_support_subset_supportχ hx
      have hχ_support_eq : Function.support χ = Metric.ball (0 : Fin n → ℝ) (R + 1) := by
        simpa [χ] using fχ.support_eq
      simpa [hχ_support_eq] using hx_supportχ
    have hφ₀_support_subset_closed :
        tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_closure : x ∈ closure (Function.support φ₀) := by
        simpa [tsupport] using hx
      have hx_supportχ : x ∈ closure (Function.support χ) :=
        closure_mono hφ₀_support_subset_supportχ hx_closure
      have hχ_support_eq : Function.support χ = Metric.ball (0 : Fin n → ℝ) (R + 1) := by
        simpa [χ] using fχ.support_eq
      have hx_ball_closure : x ∈ closure (Metric.ball (0 : Fin n → ℝ) (R + 1)) := by
        simpa [hχ_support_eq] using hx_supportχ
      exact (Metric.closure_ball_subset_closedBall :
        closure (Metric.ball (0 : Fin n → ℝ) (R + 1)) ⊆
          Metric.closedBall (0 : Fin n → ℝ) (R + 1)) hx_ball_closure
    have hφ₀_close : ∀ x, dist (φ₀ x) (g x) < δ := by
      intro x
      by_cases hxB : x ∈ B
      · have hχx : χ x = (1 : ℝ) := hχ_one x hxB
        have := hφ_raw_close x
        simpa [φ₀, hχx, dist_eq_norm, norm_sub_rev]
      · have hgx : g x = 0 := hg_zero_outside x hxB
        have h_raw : dist (φ_raw x) (g x) < δ := hφ_raw_close x
        have h_raw_norm : ‖φ_raw x‖ < δ := by
          simpa [dist_eq_norm, hgx] using h_raw
        have hφ₀_norm : ‖φ₀ x‖ < δ := by
          have hx_nonneg := hχ_nonneg x
          have hx_bound : ‖φ₀ x‖ = ‖χ x‖ * ‖φ_raw x‖ := by
            simp [φ₀]
          have hx_abs_eq : ‖χ x‖ = χ x := by
            simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
          have hx_abs_le : ‖χ x‖ ≤ 1 := by
            simpa [hx_abs_eq] using hχ_le_one x
          have hx_norm_nonneg : 0 ≤ ‖φ_raw x‖ := norm_nonneg _
          have hx_mul_le : ‖χ x‖ * ‖φ_raw x‖ ≤ ‖φ_raw x‖ :=
            (mul_le_of_le_one_left hx_norm_nonneg hx_abs_le)
          have hx_le : ‖φ₀ x‖ ≤ ‖φ_raw x‖ := by
            simpa [hx_bound]
              using hx_mul_le
          exact lt_of_le_of_lt hx_le h_raw_norm
        simpa [dist_eq_norm, hgx] using hφ₀_norm
    have h_pointwise_le : ∀ x, ‖g x - φ₀ x‖ ≤ δ := by
      intro x
      have := hφ₀_close x
      simp only [dist_eq_norm, norm_sub_rev] at this
      exact le_of_lt this
    have h_pointwise_small : ∀ x, ‖g x - φ₀ x‖ ≤ ε / 2 := by
      intro x
      exact le_trans (h_pointwise_le x) (min_le_left _ _)
    have h_pointwise_bound : ∀ x, ‖g x - φ₀ x‖ ≤ ε / (8 * denom) := by
      intro x
      exact le_trans (h_pointwise_le x) (min_le_right _ _)
    -- Cut off the preliminary approximation so that it gains compact support.
    set ψ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℝ) • φ₀ x with hψ_def
    have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ :=
      hχ_smooth.smul hφ₀_smooth
    have hψ_support : HasCompactSupport ψ :=
      (HasCompactSupport.smul_right (M := ℂ) (f := χ) hχ_support)
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    -- Relate `ψ` with the original approximation on the support of `g`.
    have hψ_eq_on_support : ∀ x ∈ tsupport g, ψ x = φ₀ x := by
      intro x hx
      have hx_ball : x ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR_subset hx
      have hχx : χ x = (1 : ℝ) := hχ_one x hx_ball
      simp [ψ, hχx]
    -- Estimate the Lᵖ error by splitting the domain into the support region
    -- and the exterior, keeping track of the uniform bounds obtained earlier.
    have h_term_support :
        eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2) := by
      have h_split :
          eLpNorm (fun x => g x - φ₀ x) p volume
              ≤
            eLpNorm (fun x => (Set.indicator B
                (fun y => g y - φ₀ y) x)) p volume
              +
            eLpNorm (fun x => (Set.indicator Bᶜ
                (fun y => g y - φ₀ y) x)) p volume := by
          let f₁ : (Fin n → ℝ) → ℂ := fun x => Set.indicator B (fun y => g y - φ₀ y) x
          let f₂ : (Fin n → ℝ) → ℂ := fun x => Set.indicator Bᶜ (fun y => g y - φ₀ y) x
          have h_partition : (fun x => g x - φ₀ x) = fun x => f₁ x + f₂ x := by
            funext x
            have hx :=
              congrArg (fun f : (Fin n → ℝ) → ℂ => f x)
                (Set.indicator_self_add_compl (s := B) (f := fun y => g y - φ₀ y))
            simp [f₁, f₂, B]
          have h_meas_base :
              AEStronglyMeasurable (fun x => g x - φ₀ x) volume :=
            (hg_cont.aestronglyMeasurable.sub
              (hφ₀_smooth.continuous.aestronglyMeasurable))
          have h_meas₁ : AEStronglyMeasurable f₁ volume :=
            h_meas_base.indicator measurableSet_closedBall
          have h_meas₂ : AEStronglyMeasurable f₂ volume :=
            h_meas_base.indicator (measurableSet_closedBall.compl)
          -- The inequality follows from the triangle inequality in `Lᵖ`.
          calc eLpNorm (fun x => g x - φ₀ x) p volume
              = eLpNorm (fun x => f₁ x + f₂ x) p volume := by rw [h_partition]
            _ ≤ eLpNorm f₁ p volume + eLpNorm f₂ p volume :=
                eLpNorm_add_le h_meas₁ h_meas₂ hp_one
      have h_ball_bound :
          eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
              < ENNReal.ofReal (ε / 4) := by
        set A := volume B ^ (1 / p.toReal) with hA_def
        have h_eLp_indicator :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                = eLpNorm (fun x => g x - φ₀ x) p (volume.restrict B) := by
          simpa using
            (eLpNorm_indicator_eq_eLpNorm_restrict
              (μ := volume) (s := B) (f := fun x => g x - φ₀ x) hB_meas)
        have h_restrict_bound :
            ∀ᵐ x ∂volume.restrict B, ‖g x - φ₀ x‖ ≤ ε / (8 * denom) :=
          (ae_of_all _ h_pointwise_bound)
        have h_eLp_le' :
            eLpNorm (fun x => g x - φ₀ x) p (volume.restrict B)
                ≤ (volume.restrict B Set.univ) ^ (1 / p.toReal) *
                    ENNReal.ofReal (ε / (8 * denom)) := by
          simpa using
            (eLpNorm_le_of_ae_bound (μ := volume.restrict B) (p := p)
              (f := fun x => g x - φ₀ x) h_restrict_bound)
        have hμB : volume.restrict B Set.univ = volume B := by
          simp [Measure.restrict_apply]
        have h_eLp_le :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                ≤ A * ENNReal.ofReal (ε / (8 * denom)) := by
          simpa [h_eLp_indicator, A, hA_def, hμB]
            using h_eLp_le'
        have hA_ne_top : A ≠ (∞ : ℝ≥0∞) := by
          simpa [A, hA_def] using h_pow_ne_top
        have hA_le : A ≤ ENNReal.ofReal denom := by
          have hA_le' : (volume B) ^ (1 / p.toReal)
              ≤ (volume S) ^ (1 / p.toReal) :=
            ENNReal.rpow_le_rpow hμB_le_S h_exponent_nonneg
          have hA_le'' : A ≤ (volume S) ^ p.toReal⁻¹ := by
            simpa [A, hA_def, one_div]
              using hA_le'
          have hS_le : (volume S) ^ p.toReal⁻¹
              ≤ ENNReal.ofReal denom := by
            have h_eq : p.toReal⁻¹ = 1 / p.toReal := (one_div _).symm
            rw [h_eq, ← ENNReal.ofReal_toReal h_powS_ne_top]
            exact ENNReal.ofReal_le_ofReal h_powS_toReal_le
          exact hA_le''.trans (by simpa [one_div] using hS_le)
        have h_mul_le :
            A * ENNReal.ofReal (ε / (8 * denom))
                ≤ ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom)) :=
          mul_le_mul_left hA_le _
        have h_mul_eq :
            ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (ε / 8) := by
          have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
          have hdenom_mul_ne_zero : (8 : ℝ) * denom ≠ 0 :=
            mul_ne_zero (by norm_num) hdenom_ne_zero
          have h_mul :
              ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                  = ENNReal.ofReal (denom * (ε / (8 * denom))) := by
            simpa using
              (ENNReal.ofReal_mul (p := denom) (q := ε / (8 * denom))
                hdenom_nonneg).symm
          have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
            have h_cancel' : ε * denom / (8 * denom) = ε / 8 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_div_mul_left (a := ε) (b := (8 : ℝ)) (c := denom)
                  hdenom_ne_zero)
            have h_rewrite :
                denom * (ε / (8 * denom)) = ε * denom / (8 * denom) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            exact h_rewrite.trans h_cancel'
          simpa [h_cancel] using h_mul
        have h_bound :
            eLpNorm (fun x => Set.indicator B (fun y => g y - φ₀ y) x) p volume
                ≤ ENNReal.ofReal (ε / 8) := by
          refine le_trans h_eLp_le ?_
          refine le_trans h_mul_le ?_
          simp [h_mul_eq]
        have hε_frac_lt_real : ε / 8 < ε / 4 := by
          have hfrac : (1 : ℝ) / 8 < 1 / 4 := by norm_num
          have hε_pos : 0 < ε := hε
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (mul_lt_mul_of_pos_left hfrac hε_pos)
        have hε_quarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have hε_frac_lt : ENNReal.ofReal (ε / 8) < ENNReal.ofReal (ε / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2
            hε_frac_lt_real
        exact lt_of_le_of_lt h_bound hε_frac_lt
      have hφ₀_zero :=
        phi0_eq_zero_outside_enlarged_ball φ₀ R hφ₀_support_subset_closed
      set f := fun x : (Fin n → ℝ) => g x - φ₀ x with hf_def
      have h_support_zero : ∀ {x : Fin n → ℝ}, x ∉ S → f x = 0 := by
        intro x hxS
        have hx_norm : R + 1 < ‖x‖ := by
          have hx_lt : ¬dist x (0 : Fin n → ℝ) ≤ R + 1 := by
            simpa [hS_def, Metric.mem_closedBall] using hxS
          have : dist x (0 : Fin n → ℝ) = ‖x‖ := by
            simp [dist_eq_norm]
          simpa [this] using lt_of_not_ge hx_lt
        have hx_not_B : x ∉ B := by
          intro hxB
          have hx_le : dist x (0 : Fin n → ℝ) ≤ R := Metric.mem_closedBall.mp hxB
          have hx_norm_le : ‖x‖ ≤ R := by
            simpa [dist_eq_norm] using hx_le
          have hR_lt : R < R + 1 := by linarith
          exact (not_le_of_gt <| lt_trans hR_lt hx_norm) hx_norm_le
        have hg_zero : g x = 0 := hg_zero_outside x hx_not_B
        have hφ₀_zero' : φ₀ x = 0 := hφ₀_zero hx_norm
        simp [hf_def, hg_zero, hφ₀_zero']
      have h_indicator_support :
          ∀ {x : Fin n → ℝ}, x ∉ S → Set.indicator Bᶜ f x = 0 := by
        intro x hxS
        by_cases hxBc : x ∈ Bᶜ
        · have hzero := h_support_zero hxS
          simp [Set.indicator, hxBc, hzero]
        · simp [Set.indicator, hxBc]
      have h_indicator_eq :
          Set.indicator Bᶜ f = Set.indicator S (Set.indicator Bᶜ f) := by
        funext x
        by_cases hxS : x ∈ S
        · simp [Set.indicator, hxS]
        · have hf_zero : f x = 0 := h_support_zero hxS
          simp [Set.indicator, hxS, hf_zero]
      have h_indicator_bound :
          ∀ᵐ x ∂volume.restrict S,
            ‖Set.indicator Bᶜ f x‖ ≤ ε / (8 * denom) :=
        Filter.Eventually.of_forall <| by
          intro x
          by_cases hxBc : x ∈ Bᶜ
          · have hx_bound := h_pointwise_bound x
            simpa [hf_def, Set.indicator, hxBc] using hx_bound
          · simp [Set.indicator, hxBc, hε_denom_nonneg]
      have h_eLp_le :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p (volume.restrict S)
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        have :=
          (eLpNorm_le_of_ae_bound (μ := volume.restrict S) (p := p)
            (f := fun x => Set.indicator Bᶜ f x) h_indicator_bound)
        simpa [Measure.restrict_apply, hS_meas, hS_def]
          using this
      have h_eLp_eq :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              = eLpNorm (fun x => Set.indicator Bᶜ f x) p (volume.restrict S) := by
        have h_congr :=
          congrArg (fun g => eLpNorm g p volume) h_indicator_eq
        have h_tmp :=
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (p := p) (s := S)
            (f := fun x => Set.indicator Bᶜ f x) hS_meas)
        exact h_congr.trans h_tmp
      have h_main_le :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [h_eLp_eq]
          using h_eLp_le
      have h_target :
          (volume S) ^ (1 / p.toReal) * ENNReal.ofReal (ε / (8 * denom))
              < ENNReal.ofReal (ε / 4) := by
        set x := ((volume S) ^ (1 / p.toReal)).toReal with hx_def
        have hx_nonneg : 0 ≤ x := ENNReal.toReal_nonneg
        have hx_eq : ENNReal.ofReal x = (volume S) ^ (1 / p.toReal) := by
          simpa [hx_def] using ENNReal.ofReal_toReal h_powS_ne_top
        have hx_le : x ≤ denom := by
          simpa [hx_def] using h_powS_toReal_le
        have hx_mul_le : x * (ε / (8 * denom)) ≤ ε / 8 := by
          have h_mul :=
            mul_le_mul_of_nonneg_right hx_le hε_denom_nonneg
          have h₁ : denom ≠ 0 := hdenom_ne_zero
          have h₂ : (8 : ℝ) ≠ 0 := by norm_num
          have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
            field_simp [h₁, h₂]
          simpa [h_cancel] using h_mul
        have hε_frac_lt_real : ε / 8 < ε / 4 := by
          have hfrac : (1 : ℝ) / 8 < 1 / 4 := by norm_num
          have hε_pos : 0 < ε := hε
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (mul_lt_mul_of_pos_left hfrac hε_pos)
        have hε_quarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have h_real_lt : x * (ε / (8 * denom)) < ε / 4 :=
          lt_of_le_of_lt hx_mul_le hε_frac_lt_real
        have h_mul_eq :
            (volume S) ^ (1 / p.toReal) * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (x * (ε / (8 * denom))) := by
          rw [← hx_eq]
          exact (ENNReal.ofReal_mul hx_nonneg).symm
        have h_mul_nonneg : 0 ≤ x * (ε / (8 * denom)) :=
          mul_nonneg hx_nonneg hε_denom_nonneg
        have h_target_real :
            ENNReal.ofReal (x * (ε / (8 * denom))) < ENNReal.ofReal (ε / 4) :=
          (ENNReal.ofReal_lt_ofReal_iff hε_quarter_pos).2 h_real_lt
        rw [h_mul_eq]
        exact h_target_real
      have h_outside_bound :
          eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
              < ENNReal.ofReal (ε / 4) := by
        simpa [hf_def]
          using
            (lt_of_le_of_lt h_main_le h_target :
              eLpNorm (fun x => Set.indicator Bᶜ f x) p volume
                < ENNReal.ofReal (ε / 4))
      have h_sum :
          eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2) := by
        have h_lt :
            eLpNorm f p volume <
              ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
          have h_sum_lt := ENNReal.add_lt_add h_ball_bound h_outside_bound
          exact (lt_of_le_of_lt h_split (by simpa [hf_def] using h_sum_lt))
        have hquarter_pos : 0 < ε / 4 := by
          have : (0 : ℝ) < 4 := by norm_num
          exact div_pos hε this
        have hquarter_nonneg : 0 ≤ ε / 4 := le_of_lt hquarter_pos
        have h_add := ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg
        have h_twice : ε / 4 + ε / 4 = ε / 2 := by ring
        have h_eq :
            ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
                = ENNReal.ofReal (ε / 2) := by
          simpa [h_twice] using h_add.symm
        simpa [hf_def, h_eq] using h_lt
      exact h_sum
    have h_term_cutoff :
        eLpNorm (fun x => φ₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2) := by
      -- The difference `φ₀ - ψ` lives where the cutoff deviates from `1`.
      -- Its support is compact, and we can bound it using the uniform estimates on `φ₀`.
      set f_cut : (Fin n → ℝ) → ℂ := fun x => φ₀ x - ψ x with hfcut_def
      have h_support_subset : Function.support φ₀ ⊆ S := by
        intro x hx
        have hx_ball := hφ₀_support_subset hx
        have hx_closed :
            x ∈ Metric.closedBall (0 : Fin n → ℝ) (R + 1) :=
          (Metric.ball_subset_closedBall :
              Metric.ball (0 : Fin n → ℝ) (R + 1)
                ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1)) hx_ball
        simpa [S, hS_def] using hx_closed
      have h_outside_zero : ∀ {x : Fin n → ℝ}, x ∉ S → f_cut x = 0 := by
        intro x hxS
        have hφ₀_zero : φ₀ x = 0 := by
          by_contra hx_nonzero
          have hx_support : x ∈ Function.support φ₀ := by
            have : φ₀ x ≠ 0 := hx_nonzero
            simpa [Function.support] using this
          exact hxS (h_support_subset hx_support)
        have hψ_zero : ψ x = 0 := by simp [ψ, hφ₀_zero]
        simp [f_cut, hφ₀_zero, hψ_zero]
      have h_pointwise_cut_le : ∀ x, ‖f_cut x‖ ≤ δ := by
        intro x
        by_cases hxB : x ∈ B
        · have hχx : χ x = (1 : ℝ) := hχ_one x hxB
          have : f_cut x = 0 := by simp [f_cut, ψ, hχx]
          simp [this, le_of_lt hδ_pos]
        · have hgx : g x = 0 := hg_zero_outside x hxB
          have hφ₀_norm : ‖φ₀ x‖ ≤ δ := by
            have h_base : ‖φ₀ x - g x‖ ≤ δ := by
              simpa [norm_sub_rev] using h_pointwise_le x
            simpa [hgx] using h_base
          have h_factored : f_cut x = ((1 - χ x) : ℝ) • φ₀ x := by
            have h := sub_smul (1 : ℝ) (χ x) (φ₀ x)
            have h' : ((1 - χ x) : ℝ) • φ₀ x = φ₀ x - ψ x := by
              simpa [ψ] using h
            simpa [f_cut, hfcut_def] using h'.symm
          have h_norm_eq : ‖f_cut x‖ = |1 - χ x| * ‖φ₀ x‖ := by
            simpa [h_factored, Real.norm_eq_abs]
              using norm_smul ((1 - χ x) : ℝ) (φ₀ x)
          have h_abs_le_one : |1 - χ x| ≤ 1 := by
            have h_nonneg : 0 ≤ 1 - χ x := by linarith [hχ_le_one x]
            have h_le : 1 - χ x ≤ 1 := by linarith [hχ_nonneg x]
            have h_abs_eq : |1 - χ x| = 1 - χ x := abs_of_nonneg h_nonneg
            simpa [h_abs_eq] using h_le
          have h_mul_le : |1 - χ x| * ‖φ₀ x‖ ≤ δ := by
            have h_le' : |1 - χ x| * ‖φ₀ x‖ ≤ ‖φ₀ x‖ := by
              have :=
                mul_le_mul_of_nonneg_right h_abs_le_one (norm_nonneg (φ₀ x))
              simpa using this
            exact h_le'.trans hφ₀_norm
          have h_norm_le : ‖f_cut x‖ ≤ δ := by
            simpa [h_norm_eq] using h_mul_le
          exact h_norm_le
      have h_pointwise_cut_bound : ∀ x, ‖f_cut x‖ ≤ ε / (8 * denom) := by
        intro x
        exact (h_pointwise_cut_le x).trans (min_le_right _ _)
      have h_ae_bound :
          ∀ᵐ x ∂volume.restrict S, ‖f_cut x‖ ≤ ε / (8 * denom) :=
        Filter.Eventually.of_forall h_pointwise_cut_bound
      have h_indicator_eq : Set.indicator S f_cut = f_cut := by
        funext x
        by_cases hxS : x ∈ S
        · simp [Set.indicator, hxS, f_cut]
        · have h_zero : f_cut x = 0 := h_outside_zero hxS
          simp [Set.indicator, hxS, f_cut, h_zero]
      have h_eLp_eq :
          eLpNorm f_cut p volume = eLpNorm f_cut p (volume.restrict S) := by
        have h_congr :=
          congrArg (fun g => eLpNorm g p volume) h_indicator_eq.symm
        have h_tmp :=
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (p := p) (s := S) (f := f_cut) hS_meas)
        exact h_congr.trans h_tmp
      have h_eLp_le_aux :
          eLpNorm f_cut p (volume.restrict S)
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [Measure.restrict_apply, hS_meas, hS_def]
          using
            (eLpNorm_le_of_ae_bound (μ := volume.restrict S) (p := p)
              (f := f_cut) h_ae_bound)
      have h_eLp_le :
          eLpNorm f_cut p volume
              ≤ (volume S) ^ (1 / p.toReal) *
                ENNReal.ofReal (ε / (8 * denom)) := by
        simpa [h_eLp_eq] using h_eLp_le_aux
      have h_le' :
          ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal)
              ≤ ENNReal.ofReal denom :=
        ENNReal.ofReal_le_ofReal h_powS_toReal_le
      have h_powS_le :
          (volume S) ^ (1 / p.toReal) ≤ ENNReal.ofReal denom := by
        have h_eq :
            (volume S) ^ (1 / p.toReal)
                = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal) :=
          (ENNReal.ofReal_toReal h_powS_ne_top).symm
        exact (le_of_eq_of_le h_eq h_le')
      have h_mul_le :
          (volume S) ^ (1 / p.toReal) *
              ENNReal.ofReal (ε / (8 * denom))
            ≤ ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom)) :=
        mul_le_mul_left h_powS_le _
      have h_mul_eq :
          ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
              = ENNReal.ofReal (ε / 8) := by
        have hdenom_ne_zero : denom ≠ 0 := ne_of_gt hdenom_pos
        have h_mul :
            ENNReal.ofReal denom * ENNReal.ofReal (ε / (8 * denom))
                = ENNReal.ofReal (denom * (ε / (8 * denom))) := by
          have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
          exact (ENNReal.ofReal_mul hdenom_nonneg).symm
        have h_cancel' : ε * denom / (8 * denom) = ε / 8 := by
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using
              (mul_div_mul_left (a := ε) (b := (8 : ℝ)) (c := denom)
                hdenom_ne_zero)
        have h_cancel : denom * (ε / (8 * denom)) = ε / 8 := by
          have h₈ : (8 : ℝ) ≠ 0 := by norm_num
          have h_denom_mul : (8 : ℝ) * denom ≠ 0 := mul_ne_zero h₈ hdenom_ne_zero
          calc denom * (ε / (8 * denom))
            = denom * ε / (8 * denom) := by rw [mul_div_assoc]
            _ = ε * denom / (8 * denom) := by rw [mul_comm denom ε]
            _ = ε / 8 := by rw [mul_div_mul_right _ _ hdenom_ne_zero]
        rw [← h_cancel]
        exact h_mul
      have h_bound :
          eLpNorm f_cut p volume ≤ ENNReal.ofReal (ε / 8) := by
        refine h_eLp_le.trans ?_
        refine h_mul_le.trans ?_
        simp [h_mul_eq]
      have h_real_lt : ε / 8 < ε / 2 := by
        calc ε / 8 = ε * (1 / 8) := div_eq_mul_one_div ε 8
          _ < ε * (1 / 2) := mul_lt_mul_of_pos_left (by norm_num : (1 : ℝ) / 8 < 1 / 2) hε
          _ = ε / 2 := (div_eq_mul_one_div ε 2).symm
      have hε_half_pos : 0 < ε / 2 := half_pos hε
      have h_lt :
          ENNReal.ofReal (ε / 8) < ENNReal.ofReal (ε / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff hε_half_pos).2 h_real_lt
      have h_bound' :
          eLpNorm (fun x => φ₀ x - ψ x) p volume ≤ ENNReal.ofReal (ε / 8) := by
        convert h_bound using 2
      exact lt_of_le_of_lt h_bound' h_lt
    have h_eLp_bound :
        eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε :=
      eLpNorm_triangle_ineq_lt p hp_one hg_cont hφ₀_smooth hψ_cont
        h_term_support h_term_cutoff hε_half
    -- `ψ` has compact support, so it automatically belongs to every Lᵖ space.
    have hψ_memLp : MemLp ψ p volume :=
      continuous_compactSupport_memLp hψ_cont hψ_support p
    refine ⟨ψ, hψ_smooth, ?_, hψ_memLp⟩
    exact h_eLp_bound
end Newton
