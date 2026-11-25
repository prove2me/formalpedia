-- Prove2me | solution 1 for GlobalTheory.T.unitary_heisenberg_radical_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:47.510967+00:00
-- url     : https://prove2.me/submissions/07d57cd3-5605-46c8-b918-dc0bf47cc38f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinatesStatement
import Theorems.Thm_P2M_GlobalTheory_InertZeta_HeisCoord_Heisenberg__94dfc0254e88


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Heis := by
  first | exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | exact GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | (intros; apply GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ <;> assumption)
end _root_.GlobalTheory.T
