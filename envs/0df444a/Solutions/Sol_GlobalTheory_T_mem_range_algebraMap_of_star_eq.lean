-- Prove2me | solution 1 for GlobalTheory.T.mem_range_algebraMap_of_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:24.910285+00:00
-- url     : https://prove2.me/submissions/ec17ae33-610a-49a5-9d2f-862d27e2f01b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeAlgebraMapOfStarEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeAlgebraMapOfStarEqStatement
import Theorems.Thm_GlobalTheory_JR_Unram_mem_range_of_star_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  first | exact @GlobalTheory.JR.Unram.mem_range_of_star_eq | exact GlobalTheory.JR.Unram.mem_range_of_star_eq | (intros; apply GlobalTheory.JR.Unram.mem_range_of_star_eq <;> assumption)
end _root_.GlobalTheory.T
