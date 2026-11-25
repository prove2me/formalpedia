-- Prove2me | solution 1 for Newton.convolution_support_ball_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:51.623825+00:00
-- url     : https://prove2.me/submissions/bde3888f-6800-4860-b35c-e67389e0a16b

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
    (f g : (Fin n → ℝ) → ℂ)
    (R δ : ℝ)
    (hf_supp : tsupport f ⊆ Metric.closedBall (0 : Fin n → ℝ) R)
    (hg_supp : tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) δ) :
    tsupport (fun x => ∫ y, f (x - y) * g y) ⊆
      Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
  set h := fun x => ∫ y, f (x - y) * g y
  have h_support_subset :
      Function.support h ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
    have h_conv_subset :
        Function.support h ⊆ Function.support g + Function.support f := by
      simpa [h, convolution, MeasureTheory.convolution, mul_comm] using
        (support_convolution_subset
          (μ := MeasureSpace.volume)
          (L := ContinuousLinearMap.mul ℝ ℂ)
          (f := g) (g := f))
    refine h_conv_subset.trans ?_
    have h_support_tsupp :
        Function.support g + Function.support f ⊆
          tsupport g + tsupport f :=
      Set.add_subset_add (subset_tsupport _) (subset_tsupport _)
    refine h_support_tsupp.trans ?_
    intro x hx
    rcases hx with ⟨u, hu, v, hv, rfl⟩
    have hu_norm : ‖u‖ ≤ δ := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hg_supp hu)
    have hv_norm : ‖v‖ ≤ R := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hf_supp hv)
    have h_norm : ‖u + v‖ ≤ R + δ := by
      have h_add : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      exact h_add.trans <| by
        simpa [add_comm] using add_le_add hu_norm hv_norm
    refine Metric.mem_closedBall.mpr ?_
    simpa [dist_eq_norm, add_comm] using h_norm
  have h_closed : IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + δ)) :=
    Metric.isClosed_closedBall
  have h_closure_subset :
      closure (Function.support h) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) :=
    closure_minimal h_support_subset h_closed
  simpa [tsupport, h] using h_closure_subset
end Newton
