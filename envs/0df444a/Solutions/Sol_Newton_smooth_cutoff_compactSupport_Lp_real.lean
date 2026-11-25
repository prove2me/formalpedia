-- Prove2me | solution 1 for Newton.smooth_cutoff_compactSupport_Lp_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:27.293786+00:00
-- url     : https://prove2.me/submissions/26614942-84eb-4b26-bcd4-6e9a31e2cd45

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
import Theorems.Thm_Newton_smooth_cutoff_compactSupport_Lp


set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (φ : ℝ → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ (2 : ℝ≥0∞) volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g (2 : ℝ≥0∞) volume ∧
      eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by
  have hn : 0 < (1 : ℕ) := by decide
  haveI := (inferInstance : FiniteDimensional ℝ (Fin 1 → ℝ))
  -- Identify `(Fin 1 → ℝ)` with ℝ.
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
  -- Transfer `φ` to `(Fin 1 → ℝ)`.
  let φF : (Fin 1 → ℝ) → ℂ := fun x => φ (E x)
  have h_pres_forward :
      MeasurePreserving (fun x : (Fin 1 → ℝ) => E x) := by
    simpa [E] using
      (volume_preserving_piUnique fun _ : Fin 1 => ℝ)
  have h_pres_symm :
      MeasurePreserving (fun t : ℝ => E.symm t) := by
    have h :=
      (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    have h_eq : (fun t : ℝ => E.symm t) = ⇑(MeasurableEquiv.piUnique fun _ : Fin 1 => ℝ).symm := by
      funext t i; fin_cases i; rfl
    rw [h_eq]; exact h
  have hφF_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φF :=
    hφ_smooth.comp (E.toLinearIsometry.contDiff)
  have hφF_memLp : MemLp φF (2 : ℝ≥0∞) volume :=
    hφ_memLp.comp_measurePreserving h_pres_forward
  obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hψ_close⟩ :=
    smooth_cutoff_compactSupport_Lp (n := 1) (p := (2 : ℝ≥0∞))
      (hp_one := by norm_num)
      (hp_ne_top := by norm_num)
      φF hφF_smooth hφF_memLp (R := R) hR_pos
      (ε := ε) hε
  let g : ℝ → ℂ := fun t => ψ (E.symm t)
  have hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g :=
    hψ_smooth.comp (E.symm.toLinearIsometry.contDiff)
  have hg_support : HasCompactSupport g :=
    hψ_support.comp_homeomorph (E.symm.toHomeomorph)
  have hg_memLp : MemLp g (2 : ℝ≥0∞) volume :=
    hψ_memLp.comp_measurePreserving h_pres_symm
  have hφψ_meas :
      AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => φF x - ψ x) volume :=
    (hφF_smooth.continuous.aestronglyMeasurable.sub
      hψ_smooth.continuous.aestronglyMeasurable)
  have hψ_close' :
      eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x) (2 : ℝ≥0∞) volume
        < ENNReal.ofReal ε := by
    simpa [Pi.sub_def, sub_eq_add_neg] using hψ_close
  have hφg_close :
      eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by
    have h_eq :=
        eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
          (p := (2 : ℝ≥0∞))
          (f := fun t : ℝ => E.symm t)
          (g := fun x : (Fin 1 → ℝ) => φF x - ψ x)
          hφψ_meas h_pres_symm
    have h_eq' :
        eLpNorm (fun t : ℝ => φ t - g t) (2 : ℝ≥0∞) volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x) (2 : ℝ≥0∞) volume := by
      simpa [Function.comp_def, φF, g, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    have h := hψ_close'
    have hφg_close' :
        eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by
      simpa [Pi.sub_def, sub_eq_add_neg] using (h_eq'.symm ▸ h)
    exact hφg_close'
  refine ⟨g, hg_smooth, hg_support, hg_memLp, ?_⟩
  simpa [Pi.sub_def, sub_eq_add_neg] using hφg_close
end Newton
