-- Prove2me | solution 1 for GlobalTheory.MinorGerm.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:06.91795+00:00
-- url     : https://prove2.me/submissions/1690c6fe-7910-4442-83e0-e864a2f20ead

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_mon_one_type
import Theorems.Thm_GlobalTheory_MinorGerm_mon_types

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
namespace GlobalTheory.MinorGerm
theorem _root_.solution : MON ∧ MONTypes := by
  exact ⟨mon_one_type, mon_types⟩
end GlobalTheory.MinorGerm
