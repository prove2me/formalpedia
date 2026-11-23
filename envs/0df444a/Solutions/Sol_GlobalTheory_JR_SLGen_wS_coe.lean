-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.wS_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:59.528614+00:00
-- url     : https://prove2.me/submissions/96377309-677b-46fc-bf8c-80f3dede5554

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SLGen
variable {F : Type} [Field F]
namespace GlobalTheory.JR.SLGen
theorem _root_.solution : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
end GlobalTheory.JR.SLGen
