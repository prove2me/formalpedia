-- Prove2me | solution 1 for Newton.smooth_compactSupport_dense_L1_L2_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:13.709643+00:00
-- url     : https://prove2.me/submissions/884c2d0e-bb98-491e-bf5a-e79f7cc4cd00

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
import Theorems.Thm_Newton_schwartz_dense_L1_L2_simultaneous
import Theorems.Thm_Newton_smooth_cutoff_compactSupport_L1_L2_real

set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by
  -- We identify ℝ with the one-dimensional euclidean space `Fin 1 → ℝ`.
  have hn : 0 < (1 : ℕ) := by decide
  -- The linear isometry equivalence between `(Fin 1 → ℝ)` and `ℝ` given by evaluation at 0.
  let E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ :=
    { toLinearEquiv :=
        { toFun := fun x => x 0
          invFun := fun t _ => t
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl
          left_inv := by
            intro x
            funext i
            have : i = (0 : Fin 1) := Subsingleton.elim _ _
            simp [this]
          right_inv := by intro t; rfl }
      norm_map' := by
        intro x
        have hx_const : x = fun _ : Fin 1 => x 0 := by
          funext i
          have : i = (0 : Fin 1) := Subsingleton.elim _ _
          simp [this]
        have hx_norm' : ‖fun _ : Fin 1 => x 0‖ = ‖x‖ := by
          simpa using congrArg norm hx_const.symm
        have hx_norm'' : ‖fun _ : Fin 1 => x 0‖ = ‖x 0‖ := by
          simp
        have hx_norm : ‖x‖ = ‖x 0‖ := by
          simpa [hx_norm''] using hx_norm'.symm
        simp [hx_norm.symm] }
  -- Transport the original function to `(Fin 1 → ℝ)`.
  let F : (Fin 1 → ℝ) → ℂ := fun x => f (E x)
  -- `f` belongs to both L¹ and L², hence so does `F` by measure preservation.
  have h_pres : MeasurePreserving (fun t : ℝ => E.symm t) := by
    have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    have h_eq : (fun t : ℝ => E.symm t) = ⇑(MeasurableEquiv.piUnique fun _ : Fin 1 => ℝ).symm := by
      funext t i; fin_cases i; rfl
    rw [h_eq]; exact h
  have hF_L1 : MemLp F 1 volume :=
    ((memLp_one_iff_integrable (μ := volume)).mpr hf_L1).comp_measurePreserving
      (by
        simpa [E] using
          (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)))
  have hF_L2 : MemLp F 2 volume :=
    hf_L2.comp_measurePreserving
      (by
        simpa [E] using
          (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)))
  -- Use the simultaneous Schwartz approximation on `(Fin 1 → ℝ)` with a small error budget.
  obtain ⟨φ, hφ_L1, hφ_L2⟩ :=
    schwartz_dense_L1_L2_simultaneous (n := 1) F hF_L1 hF_L2
      (ε := ε / 4) (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 4))
  -- Turn the Schwartz approximation `φ` into a function on ℝ.
  let φℝ : ℝ → ℂ := fun t => φ (E.symm t)
  have hφℝ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φℝ :=
    (φ.smooth (⊤ : ℕ∞)).comp (E.symm.toLinearIsometry.contDiff)
  have hφℝ_memLp₁ : MemLp φℝ 1 volume :=
    (φ.memLp (p := (1 : ℝ≥0∞)) (μ := volume)).comp_measurePreserving h_pres
  have hφℝ_memLp₂ : MemLp φℝ 2 volume :=
    (φ.memLp (p := (2 : ℝ≥0∞)) (μ := volume)).comp_measurePreserving h_pres
  have hFφ_meas :
      AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => F x - φ x) volume :=
    (hF_L2.aestronglyMeasurable.sub
      (φ.smooth (⊤ : ℕ∞)).continuous.aestronglyMeasurable)
  -- Smoothly cut off `φℝ` to obtain a compactly supported function while controlling the error.
  obtain ⟨g, hg_smooth, hg_support, hg_memLp, hg_close_L1, hg_close_L2⟩ :=
    smooth_cutoff_compactSupport_L1_L2_real φℝ hφℝ_smooth hφℝ_memLp₁ hφℝ_memLp₂
      (R := 1) (hR_pos := by norm_num)
      (ε := ε / 4)
      (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 4))
  -- Control the L¹ and L² errors simultaneously via triangle inequalities.
  have hφ_L1' :
      eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 1 volume < ENNReal.ofReal (ε / 4) := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hφ_L1
  have hφ_L2' :
      eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 2 volume < ENNReal.ofReal (ε / 4) := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hφ_L2
  have hfφ_L1 : eLpNorm (fun t => f t - φℝ t) 1 volume < ENNReal.ofReal (ε / 4) := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (1 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => F x - φ x)
          hFφ_meas h_pres
    have h_eq' :
        eLpNorm (fun t : ℝ => f t - φℝ t) 1 volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 1 volume := by
      simpa [Function.comp_def, F, φℝ, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    simpa [h_eq'] using hφ_L1'
  have hfφ_L2 : eLpNorm (fun t => f t - φℝ t) 2 volume < ENNReal.ofReal (ε / 4) := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (2 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => F x - φ x)
          hFφ_meas h_pres
    have h_eq' :
        eLpNorm (fun t : ℝ => f t - φℝ t) 2 volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => F x - φ x) 2 volume := by
      simpa [Function.comp_def, F, φℝ, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    simpa [h_eq'] using hφ_L2'
  have hφg_L1 : eLpNorm (fun t => φℝ t - g t) 1 volume < ENNReal.ofReal (ε / 4) :=
    hg_close_L1
  have hφg_L2 : eLpNorm (fun t => φℝ t - g t) 2 volume < ENNReal.ofReal (ε / 4) :=
    hg_close_L2
  have hf_meas : AEStronglyMeasurable f volume := hf_L2.aestronglyMeasurable
  have hφℝ_meas : AEStronglyMeasurable φℝ volume :=
    (hφℝ_smooth.continuous).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume :=
    (hg_smooth.continuous).aestronglyMeasurable
  have hfg_meas :
      AEStronglyMeasurable (fun t => f t - φℝ t) volume :=
    hf_meas.sub hφℝ_meas
  have hφg_meas :
      AEStronglyMeasurable (fun t => φℝ t - g t) volume :=
    hφℝ_meas.sub hg_meas
  have hfg_fun_eq :
      (fun t => f t - g t)
        = (fun t => f t - φℝ t) + fun t => φℝ t - g t := by
    funext t
    have : f t - g t = (f t - φℝ t) + (φℝ t - g t) := by ring
    simp [Pi.add_apply]
  have hfg_triangle :
      eLpNorm (fun t => f t - g t) 2 volume
        ≤ eLpNorm (fun t => f t - φℝ t) 2 volume
            + eLpNorm (fun t => φℝ t - g t) 2 volume := by
    simpa [hfg_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
          (f := fun t => f t - φℝ t) (g := fun t => φℝ t - g t)
          hfg_meas hφg_meas
          (by
            have : (1 : ℝ) ≤ 2 := by norm_num
            exact_mod_cast this))
  have hfg_triangle_L1 :
      eLpNorm (fun t => f t - g t) 1 volume
        ≤ eLpNorm (fun t => f t - φℝ t) 1 volume
            + eLpNorm (fun t => φℝ t - g t) 1 volume := by
    simpa [hfg_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
          (f := fun t => f t - φℝ t) (g := fun t => φℝ t - g t)
          hfg_meas hφg_meas
          (by
            have : (1 : ℝ) ≤ 1 := le_rfl
            exact_mod_cast this))
  have h_sum_lt :
      eLpNorm (fun t => f t - φℝ t) 2 volume
            + eLpNorm (fun t => φℝ t - g t) 2 volume
        < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    ENNReal.add_lt_add hfφ_L2 hφg_L2
  have h_sum_lt_L1 :
      eLpNorm (fun t => f t - φℝ t) 1 volume
            + eLpNorm (fun t => φℝ t - g t) 1 volume
        < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    ENNReal.add_lt_add hfφ_L1 hφg_L1
  have hfg_L2_half :
      eLpNorm (fun t => f t - g t) 2 volume
        < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    lt_of_le_of_lt hfg_triangle h_sum_lt
  have hfg_L1_half :
      eLpNorm (fun t => f t - g t) 1 volume
        < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    lt_of_le_of_lt hfg_triangle_L1 h_sum_lt_L1
  have hε_quarter_pos : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  have h_add_eq :
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
        = ENNReal.ofReal (ε / 2) := by
    have hnonneg : 0 ≤ ε / 4 := le_of_lt hε_quarter_pos
    have h_sum : ε / 4 + ε / 4 = ε / 2 := by ring
    simpa [h_sum]
      using (ENNReal.ofReal_add hnonneg hnonneg).symm
  have hfg_L2_half' :
      eLpNorm (fun t => f t - g t) 2 volume
        < ENNReal.ofReal (ε / 2) := by
    simpa [h_add_eq] using hfg_L2_half
  have hfg_L1_half' :
      eLpNorm (fun t => f t - g t) 1 volume
        < ENNReal.ofReal (ε / 2) := by
    simpa [h_add_eq] using hfg_L1_half
  have hε_half_pos : 0 < ε / 2 := half_pos hε
  have hε_half_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)
  have hfg_L2 :
      eLpNorm (fun t => f t - g t) 2 volume < ENNReal.ofReal ε :=
    lt_trans hfg_L2_half' hε_half_lt
  have hfg_L1 :
      eLpNorm (fun t => f t - g t) 1 volume < ENNReal.ofReal ε :=
    lt_trans hfg_L1_half' hε_half_lt
  refine ⟨g, hg_smooth, hg_support, hfg_L1, hfg_L2⟩
end Newton
