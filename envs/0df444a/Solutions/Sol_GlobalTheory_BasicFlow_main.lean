-- Prove2me | solution 1 for GlobalTheory.BasicFlow.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:57.436275+00:00
-- url     : https://prove2.me/submissions/858c2989-d9f9-49db-915d-3db3c1a41447

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
import Theorems.Thm_GlobalTheory_BasicFlow_dropLevelsBasic
import Theorems.Thm_GlobalTheory_BasicFlow_splitLarge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution : DropLevelsBasic ∧ SplitLarge := ⟨dropLevelsBasic, splitLarge⟩
end GlobalTheory.BasicFlow
