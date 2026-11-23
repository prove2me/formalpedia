-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.nS_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:25.806279+00:00
-- url     : https://prove2.me/submissions/a3ace1ae-4a1a-4209-b6fb-071e47608a33

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
theorem _root_.solution (z : F) : ((nS z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] := rfl
end GlobalTheory.JR.SLGen
