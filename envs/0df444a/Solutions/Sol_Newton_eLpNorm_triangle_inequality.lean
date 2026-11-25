-- Prove2me | solution 1 for Newton.eLpNorm_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:06.966265+00:00
-- url     : https://prove2.me/submissions/e545bac7-9a3f-48cd-b8a5-f9d2be1a36c8

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g h : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgh : AEStronglyMeasurable (fun x => g x - h x) volume) :
    eLpNorm (fun x => f x - h x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - h x) p volume := by
  have h_decomp :
      (fun x => f x - h x) =
        (fun x => f x - g x) + fun x => g x - h x := by
    funext x
    simp [sub_eq_add_neg, add_left_comm, add_assoc]
  simpa [h_decomp] using
    (eLpNorm_add_le (μ := volume) (p := p)
      (f := fun x => f x - g x)
      (g := fun x => g x - h x)
      hfg hgh hp)
end Newton
