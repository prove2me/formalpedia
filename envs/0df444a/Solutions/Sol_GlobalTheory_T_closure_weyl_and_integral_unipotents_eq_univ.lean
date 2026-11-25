-- Prove2me | solution 1 for GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:09.261061+00:00
-- url     : https://prove2.me/submissions/0904b6f6-bc2c-40b2-8959-d32fa9985f72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotentStatement
import Theorems.Thm_GlobalTheory_JR_sl2_closure_weyl_unipotent_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  first | exact @GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | exact GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | (intros; apply GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top <;> assumption)
end _root_.GlobalTheory.T
