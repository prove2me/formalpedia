-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.hasDerivAt_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:12.790227+00:00
-- url     : https://prove2.me/submissions/4cf5fe27-8b76-4da6-a1d0-d639d85ff21d

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
theorem _root_.solution (a : ℝ) : HasDerivAt (fun t : ℝ => (π * I * ((t * a : ℝ) : ℂ))) (π * I * a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * a : ℝ) : ℂ)) (a : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp
  exact h1.const_mul (π * I)
end GlobalTheory.Mem.Lift.DCalc
