-- Prove2me | solution 1 for Newton.smooth_cutoff_compactSupport_Lp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:11.177275+00:00
-- url     : https://prove2.me/submissions/c5a00223-f177-4759-8da5-6b40937a0fcb

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Theorems.Thm_Newton_continuous_compactSupport_dense_Lp
import Theorems.Thm_Newton_smooth_cutoff_compactSupport_Lp_aux

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hp_ne_top : p ≠ ⊤)
    (φ : (Fin n → ℝ) → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ p volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧ MemLp ψ p volume ∧
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε := by
  have _ := hR_pos
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  obtain ⟨g, hg_cont, hg_compact, hg_memLp, hφg⟩ :=
    continuous_compactSupport_dense_Lp
      (p := p) (hp_ne_top := hp_ne_top)
      φ hφ_memLp (ε := ε / 4) hε_quarter_pos
  obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hgψ⟩ :=
    smooth_cutoff_compactSupport_Lp_aux (p := p) (hp_one := hp_one)
      g hg_cont hg_compact (ε := ε / 4) hε_quarter_pos
  have hφg_le :
      eLpNorm (fun x => φ x - g x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hφg
  have hgψ_le :
      eLpNorm (fun x => g x - ψ x) p volume ≤ ENNReal.ofReal (ε / 4) :=
    le_of_lt hgψ
  have hφg_meas :
      AEStronglyMeasurable (fun x => φ x - g x) volume :=
    hφ_smooth.continuous.aestronglyMeasurable.sub hg_cont.aestronglyMeasurable
  have hgψ_meas :
      AEStronglyMeasurable (fun x => g x - ψ x) volume :=
    hg_cont.aestronglyMeasurable.sub hψ_smooth.continuous.aestronglyMeasurable
  have h_fun_eq :
      (fun x => φ x - ψ x)
        = (fun x => φ x - g x) + fun x => g x - ψ x := by
    funext x; simp [sub_eq_add_neg, add_left_comm, add_assoc]
  have h_triangle :
      eLpNorm (fun x => φ x - ψ x) p volume
        ≤ eLpNorm (fun x => φ x - g x) p volume
            + eLpNorm (fun x => g x - ψ x) p volume := by
    simpa [h_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := p)
          (f := fun x => φ x - g x)
          (g := fun x => g x - ψ x)
          (hf := hφg_meas) (hg := hgψ_meas) hp_one)
  have h_add_le :
      eLpNorm (fun x => φ x - g x) p volume
            + eLpNorm (fun x => g x - ψ x) p volume
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    add_le_add hφg_le hgψ_le
  have h_total_le :
      eLpNorm (fun x => φ x - ψ x) p volume
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    h_triangle.trans h_add_le
  have h_add_eq :
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (ε / 2) := by
    have hnonneg : 0 ≤ ε / 4 := le_of_lt hε_quarter_pos
    have h_sum : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_add := ENNReal.ofReal_add hnonneg hnonneg
    simpa [h_sum] using h_add.symm
  have h_total_le' :
      eLpNorm (fun x => φ x - ψ x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    simpa [h_add_eq] using h_total_le
  have hε_half_lt_real : ε / 2 < ε := by
    have : (0 : ℝ) < ε := hε
    linarith
  have hε_half_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 hε_half_lt_real
  have h_total_lt :
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt h_total_le' hε_half_lt
  exact ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, h_total_lt⟩
end Newton
