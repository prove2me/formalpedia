-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:55.024159+00:00
-- url     : https://prove2.me/submissions/4068e539-17cd-4e80-8b5c-fa59404b061c

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
namespace GlobalTheory.Mem.Lift.DCalc
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E} (hF : Differentiable ℝ F)
    (w y : V) : HasDerivAt (fun t : ℝ => F (w + t • y)) (fderiv ℝ F w y) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add w
  have hF' : HasFDerivAt F (fderiv ℝ F w) (w + (0 : ℝ) • y) := by
    simpa using (hF w).hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl
end GlobalTheory.Mem.Lift.DCalc
