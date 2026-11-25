-- Prove2me | solution 1 for Newton.convolution_diff_bound_L2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:18.479247+00:00
-- url     : https://prove2.me/submissions/1bee591a-d3c2-4490-b5d3-1a84929fc9a4

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Theorems.Thm_Newton_convolution_sub
import Theorems.Thm_Newton_convolution_fiber_integrable_L2_L1
import Theorems.Thm_Newton_young_convolution_inequality


set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hf₂ : MemLp f₂ 2 volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by
  -- Lebesgue measure on ℝ^n is neg-invariant; provide the instance locally for this section.
  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant := by
    let μ : Measure (Fin n → ℝ) := volume
    refine ⟨?_⟩
    set T := (-1 : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have h_det_eq :
        LinearMap.det T =
          (-1 : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
      simpa [T]
        using
          (LinearMap.det_smul (-1 : ℝ)
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    have h_abs_det : abs (LinearMap.det T) = (1 : ℝ) := by
      simp [h_det_eq]
    have h_det_ne_zero : LinearMap.det T ≠ 0 := by
      have h_abs_ne : abs (LinearMap.det T) ≠ 0 := by
        simp [h_abs_det]
      exact abs_ne_zero.mp h_abs_ne
    have h_map_aux :=
      Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := T) h_det_ne_zero
    have h_abs_inv : abs ((LinearMap.det T)⁻¹) = (1 : ℝ) := by
      have := abs_inv (LinearMap.det T)
      simp [h_abs_det]
    have h_scalar :
        ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) = (1 : ℝ≥0∞) := by
      simp [h_abs_inv]
    have h_T_eq_neg : (T : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => -y := by
      funext y
      simp [T]
    have h_map :
        Measure.map (fun y : (Fin n → ℝ) => -y) volume = volume := by
      calc Measure.map (fun y : (Fin n → ℝ) => -y) volume
          = Measure.map T volume := by rw [h_T_eq_neg]
        _ = ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) • volume := h_map_aux
        _ = (1 : ℝ≥0∞) • volume := by rw [h_scalar]
        _ = volume := one_smul _ _
    have h_neg_eq_neg : (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => -y := by
      rfl
    have h_neg_eq :
        Measure.neg (μ := (volume : Measure (Fin n → ℝ))) = volume := by
      unfold Measure.neg
      rw [h_neg_eq_neg]
      exact h_map
    exact h_neg_eq
  -- Establish a.e. integrability of the two convolution integrands
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    simpa using
      (convolution_fiber_integrable_L2_L1 (μ := volume) (f := f₁) (g := ψ) hf₁ hψ)
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    simpa using
      (convolution_fiber_integrable_L2_L1 (μ := volume) (f := f₂) (g := ψ) hf₂ hψ)
  -- Rewrite the difference of convolutions as the convolution of the difference
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume := by
    simpa using eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) h_sub_ae.symm
  -- Apply Young's inequality in the L² × L¹ → L² form
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 2 volume := hf₁.sub hf₂
  have hYoung := by
    have hg1 : MemLp ψ 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hψ
    have h :=
      young_convolution_inequality (f := f₁ - f₂) (g := ψ)
        (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
        (hp := by norm_num) (hq := by simp) (hpqr := by simp [one_div, add_comm])
        hdiff_mem hg1
    simpa using h
  have h_bound :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume :=
    hYoung.2
  -- Assemble the estimate using the a.e. equality
  simpa [h_eq_eLp] using h_bound
end Newton
