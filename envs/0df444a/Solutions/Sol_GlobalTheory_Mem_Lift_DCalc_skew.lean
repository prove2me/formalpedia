-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:55.122746+00:00
-- url     : https://prove2.me/submissions/97de62a0-d7fd-425c-a66b-26e3247d0a46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.DCalc
theorem _root_.solution (h0 : ∀ x, om x x = 0) (x y : V) : om y x = -om x y := by
  have hxy := h0 (x + y)
  simp only [map_add, _root_.add_apply, h0] at hxy
  linarith
end GlobalTheory.Mem.Lift.DCalc
