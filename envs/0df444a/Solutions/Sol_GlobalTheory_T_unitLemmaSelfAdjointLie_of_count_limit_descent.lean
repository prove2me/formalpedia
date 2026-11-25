-- Prove2me | solution 1 for GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:40.928934+00:00
-- url     : https://prove2.me/submissions/c71dcbdc-6423-4639-97cf-3f1f1efd5fbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_unitLemmaLie_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
end _root_.GlobalTheory.T
