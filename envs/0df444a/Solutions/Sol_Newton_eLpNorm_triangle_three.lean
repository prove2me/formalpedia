-- Prove2me | solution 1 for Newton.eLpNorm_triangle_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:35:50.030975+00:00
-- url     : https://prove2.me/submissions/864d51c5-02f0-4b69-a75c-b0da68d65fa2

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Theorems.Thm_Newton_eLpNorm_triangle_inequality

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g ψ φ : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgψ : AEStronglyMeasurable (fun x => g x - ψ x) volume)
    (hψφ : AEStronglyMeasurable (fun x => ψ x - φ x) volume) :
    eLpNorm (fun x => f x - φ x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - ψ x) p volume +
    eLpNorm (fun x => ψ x - φ x) p volume := by
  have hgφ : AEStronglyMeasurable (fun x => g x - φ x) volume := by
    have h_sum := hgψ.add hψφ
    have h_eq :
        (fun x => g x - φ x) =
          (fun x => g x - ψ x) + fun x => ψ x - φ x := by
      funext x
      simp [sub_eq_add_neg, add_left_comm, add_assoc]
    simpa [h_eq] using h_sum
  have h_triangle₁ :=
    eLpNorm_triangle_inequality (f := f) (g := g) (h := φ) (p := p) hp hfg hgφ
  have h_triangle₂ :=
    eLpNorm_triangle_inequality (f := g) (g := ψ) (h := φ) (p := p) hp hgψ hψφ
  refine h_triangle₁.trans ?_
  have h_add := add_le_add_left h_triangle₂ (eLpNorm (fun x => f x - g x) p volume)
  simpa [add_comm, add_left_comm, add_assoc] using h_add
end Newton
