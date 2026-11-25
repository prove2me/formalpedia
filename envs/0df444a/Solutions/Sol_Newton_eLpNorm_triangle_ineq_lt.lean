-- Prove2me | solution 1 for Newton.eLpNorm_triangle_ineq_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:50.691204+00:00
-- url     : https://prove2.me/submissions/ec1ac93c-aa92-4bb0-8116-9c1d30b5a6c1

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {g φ₀ ψ : (Fin n → ℝ) → ℂ}
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hg_cont : Continuous g)
    (hφ₀_smooth : ContDiff ℝ ∞ φ₀)
    (hψ_cont : Continuous ψ)
    {ε : ℝ}
    (h_term_support : eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2))
    (h_term_cutoff : eLpNorm (fun x => φ₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2))
    (hε_half : 0 < ε / 2) :
    eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by
  have h_meas₁ : AEStronglyMeasurable (fun x => g x - φ₀ x) volume :=
    hg_cont.aestronglyMeasurable.sub hφ₀_smooth.continuous.aestronglyMeasurable
  have h_meas₂ : AEStronglyMeasurable (fun x => φ₀ x - ψ x) volume :=
    hφ₀_smooth.continuous.aestronglyMeasurable.sub hψ_cont.aestronglyMeasurable
  have h_fun_eq :
      (fun x => g x - ψ x)
        = (fun x => g x - φ₀ x) + fun x => φ₀ x - ψ x := by
    funext x; simp [sub_eq_add_neg, add_left_comm, add_assoc]
  have h_triangle :
      eLpNorm (fun x => g x - ψ x) p volume
          ≤
        eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume := by
    simpa [h_fun_eq] using
      (eLpNorm_add_le (μ := volume) (p := p)
        (f := fun x => g x - φ₀ x)
        (g := fun x => φ₀ x - ψ x)
        (hf := h_meas₁) (hg := h_meas₂) hp_one)
  have h_lt0 :
      eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume
        < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add h_term_support h_term_cutoff
  have h_half_nonneg : 0 ≤ ε / 2 := le_of_lt hε_half
  have h_add := ENNReal.ofReal_add h_half_nonneg h_half_nonneg
  have h_twice : ε / 2 + ε / 2 = ε := by ring
  have h_target :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          = ENNReal.ofReal ε := by
    calc
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)
          = ENNReal.ofReal (ε / 2 + ε / 2) := by
            simpa [add_comm, add_left_comm, add_assoc] using h_add.symm
      _ = ENNReal.ofReal ε := by simp [h_twice]
  have h_sum_lt :
      eLpNorm (fun x => g x - φ₀ x) p volume
          + eLpNorm (fun x => φ₀ x - ψ x) p volume
        < ENNReal.ofReal ε := by
    simpa [h_target] using h_lt0
  exact lt_of_le_of_lt h_triangle h_sum_lt
end Newton
