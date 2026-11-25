-- Prove2me | solution 1 for Newton.convolution_diff_bound_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:50:16.1398+00:00
-- url     : https://prove2.me/submissions/1c0ffde9-5198-4fd6-b37a-62f281b90974

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Theorems.Thm_Newton_convolution_sub
import Theorems.Thm_Newton_convolution_kernel_integrable
import Theorems.Thm_Newton_young_convolution_inequality


set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : Integrable f₁ volume)
    (hf₂ : Integrable f₂ volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
  -- Rewrite the difference of convolutions as the convolution of the difference.
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₁) (g := ψ) hf₁ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₂) (g := ψ) hf₂ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂
  -- Use ae-equality to replace the L¹ norm by the convolution of the difference.
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume := by
    -- note the equality in `convolution_sub` has the opposite orientation
    simpa using
      eLpNorm_congr_ae (μ := volume) (p := (1 : ℝ≥0∞)) h_sub_ae.symm
  -- Apply Young (L¹×L¹→L¹) to the convolution of the difference with ψ.
  have hdiff_int : Integrable (fun x => f₁ x - f₂ x) volume := hf₁.sub hf₂
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hdiff_int
  have hψ_mem : MemLp ψ 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hψ
  have h_young :=
    young_convolution_inequality
      (f := fun x => f₁ x - f₂ x) (g := ψ)
      (p := (1 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (hp := by simp) (hq := by simp) (hpqr := by simp)
      hdiff_mem hψ_mem
  have :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
    simpa using h_young.2
  simpa [h_eq_eLp] using this
end Newton
