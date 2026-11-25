-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.integral_inv_ofReal_add_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:50.502846+00:00
-- url     : https://prove2.me/submissions/3f64b933-a542-47b8-8e35-81d4ed62570b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_ofReal_add_mul_I_ne_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_invPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I)⁻¹ = invPrimitive c b - invPrimitive c a := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_invPrimitive hc x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact (continuous_ofReal.add continuous_const).inv₀ (ofReal_add_mul_I_ne_zero hc)
end GroundTheory.Global.Elliptic
