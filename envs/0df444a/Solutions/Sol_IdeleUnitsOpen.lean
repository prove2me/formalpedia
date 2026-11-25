-- Prove2me | solution 1 for IdeleUnitsOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:14.208716+00:00
-- url     : https://prove2.me/submissions/6526f27b-26e1-4600-83ff-a0f88111ad3e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IdeleUnitsOpen
import Theorems.Thm_PI_IdeleUnitsOpenW_openUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (L : Type) [Field L] [NumberField L] : Formalism.L2.Host.CharEx.OpenUnits L :=
  PI.IdeleUnitsOpenW.openUnits L
