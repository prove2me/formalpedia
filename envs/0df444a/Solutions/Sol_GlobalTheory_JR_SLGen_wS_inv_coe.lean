-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.wS_inv_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:48.859985+00:00
-- url     : https://prove2.me/submissions/8ebe7f13-52a1-494b-9ad9-7311a8ab7ec7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Theorems.Thm_GlobalTheory_JR_SLGen_wS_coe

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
theorem _root_.solution :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wS_coe, Matrix.adjugate_fin_two]; simp
end GlobalTheory.JR.SLGen
