-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.hasDerivAt_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:03.873525+00:00
-- url     : https://prove2.me/submissions/f06c95a5-f51f-41e5-8853-6bae64c1ec5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_lin

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
theorem _root_.solution (a : ℝ) {G : ℝ → B} {G' : B} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) (G' + (π * I * a : ℂ) • G 0) 0 := by
  have hc := (hasDerivAt_lin a).cexp
  have hp : HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) _ 0 := hc.smul hG
  convert hp using 1
  simp
end GlobalTheory.Mem.Lift.DCalc
