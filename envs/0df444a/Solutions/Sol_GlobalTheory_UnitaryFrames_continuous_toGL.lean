-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.continuous_toGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.210388+00:00
-- url     : https://prove2.me/submissions/7e1fbd14-9204-4507-9046-dacc89fcac10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Theorems.Thm_GlobalTheory_UnitaryFrames_val_toGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitaryFrames
theorem _root_.solution {r : ℕ} (X : Data E r) :
    Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => toGL X x.2 := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => mat x.1 τ :=
    (continuous_apply τ).comp continuous_subtype_val
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have h : (fun x : {x : Frame X.Ψ r | IsOrth X x} =>
      (((toGL X x.2 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
      fun x => ((mat x.1 τ).det)⁻¹ • (mat x.1 τ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_toGL, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hc.matrix_det.inv₀ fun x => det_ne_zero_of_isOrth X x.2 τ).smul hc.matrix_adjugate
end GlobalTheory.UnitaryFrames
