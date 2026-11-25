-- Prove2me | solution 1 for Newton.triangle_inequality_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:36:46.140404+00:00
-- url     : https://prove2.me/submissions/1fb411a3-326b-45eb-a93e-bd8d13b907a8

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity

set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g h : (Fin n → ℝ) → ℂ)
    (ε ε₁ ε₂ ε₃ : ℝ)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hh_meas : AEStronglyMeasurable h volume)
    (hf : eLpNorm f (1 : ℝ≥0∞) volume < ENNReal.ofReal ε₁)
    (hg : eLpNorm g 1 volume < ENNReal.ofReal ε₂)
    (hh : eLpNorm h 1 volume < ENNReal.ofReal ε₃)
    (h_sum : ε₁ + ε₂ + ε₃ ≤ ε) :
    eLpNorm (fun x => f x + g x + h x) 1 volume < ENNReal.ofReal ε := by
  -- First, apply the triangle inequality twice.
  have h_fg :
      eLpNorm (fun x => f x + g x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm g 1 volume := by
    exact eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hf_meas hg_meas le_rfl
  have h_gh :
      eLpNorm (fun x => g x + h x) 1 volume
        ≤ eLpNorm g 1 volume + eLpNorm h 1 volume := by
    exact eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hg_meas hh_meas le_rfl
  have h_total_aux :
      eLpNorm (fun x => f x + (g x + h x)) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm (fun x => g x + h x) 1 volume := by
    have h_sum_meas : AEStronglyMeasurable (fun x => g x + h x) volume :=
      hg_meas.add hh_meas
    exact eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞)) hf_meas h_sum_meas le_rfl
  have h_total :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm (fun x => g x + h x) 1 volume := by
    have h_rewrite :
        (fun x => f x + g x + h x)
          = fun x => f x + (g x + h x) := by
      funext x; simp [add_comm, add_left_comm]
    simpa [h_rewrite] using h_total_aux
  have h_total_le :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        ≤ eLpNorm f 1 volume + eLpNorm g 1 volume + eLpNorm h 1 volume := by
    have h_aux := add_le_add_left h_gh (eLpNorm f 1 volume)
    exact h_total.trans <| by
      simpa [add_comm, add_left_comm, add_assoc] using h_aux
  -- Each εᵢ must be positive, otherwise the inequalities `hf`, `hg`, `hh` are impossible.
  have hε₁_pos : 0 < ε₁ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₁ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm f 1 volume < 0 := by simp [h_zero] at hf
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm f 1 volume from bot_le)) this
  have hε₂_pos : 0 < ε₂ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₂ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm g 1 volume < 0 := by simp [h_zero] at hg
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm g 1 volume from bot_le)) this
  have hε₃_pos : 0 < ε₃ := by
    by_contra hle
    have h_zero : ENNReal.ofReal ε₃ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
    have : eLpNorm h 1 volume < 0 := by simp [h_zero] at hh
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ eLpNorm h 1 volume from bot_le)) this
  -- Combine the three individual bounds.
  have h_sum_fg :
      eLpNorm f 1 volume + eLpNorm g 1 volume
        < ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ :=
    ENNReal.add_lt_add hf hg
  have h_sum_total :
      eLpNorm f 1 volume + eLpNorm g 1 volume + eLpNorm h 1 volume
        < ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃ := by
    -- Rearrange to use `ENnreal.add_lt_add` twice.
    have := ENNReal.add_lt_add h_sum_fg hh
    simpa [add_comm, add_left_comm, add_assoc]
      using this
  -- Rewrite the right-hand side using real addition.
  have h_ofReal_fg :
      ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂
        = ENNReal.ofReal (ε₁ + ε₂) :=
    (ENNReal.ofReal_add (le_of_lt hε₁_pos) (le_of_lt hε₂_pos)).symm
  have h_ofReal_total :
      ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ + ENNReal.ofReal ε₃
        = ENNReal.ofReal (ε₁ + ε₂ + ε₃) := by
    have h_nonneg : 0 ≤ ε₁ + ε₂ := add_nonneg hε₁_pos.le hε₂_pos.le
    simpa [h_ofReal_fg, add_comm, add_left_comm, add_assoc]
      using (ENNReal.ofReal_add h_nonneg hε₃_pos.le).symm
  have h_target :
      eLpNorm (fun x => f x + g x + h x) 1 volume
        < ENNReal.ofReal (ε₁ + ε₂ + ε₃) := by
    refine lt_of_le_of_lt h_total_le ?_
    simpa [h_ofReal_total] using h_sum_total
  -- Use the assumption on ε₁ + ε₂ + ε₃ ≤ ε.
  have h_sum_nonneg : 0 ≤ ε₁ + ε₂ + ε₃ :=
    add_nonneg (add_nonneg hε₁_pos.le hε₂_pos.le) hε₃_pos.le
  have hε_nonneg : 0 ≤ ε := le_trans h_sum_nonneg h_sum
  have h_bound :
      ENNReal.ofReal (ε₁ + ε₂ + ε₃) ≤ ENNReal.ofReal ε :=
    (ENNReal.ofReal_le_ofReal_iff (q := ε) hε_nonneg).mpr h_sum
  exact lt_of_lt_of_le h_target h_bound
end Newton
