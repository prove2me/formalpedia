-- Prove2me | solution 1 for GlobalTheory.T.capelli_operator_unitaryGroup_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:20:11.878917+00:00
-- url     : https://prove2.me/submissions/f358ef08-25e2-4023-9960-976076269899

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CapelliOperatorUnitaryGroupLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CapelliOperatorUnitaryGroupLocalStatement
import Theorems.Thm_GlobalTheory_CapelliLocality_capelliH_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)
end _root_.GlobalTheory.T
