-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:36.393551+00:00
-- url     : https://prove2.me/submissions/9c0f23d4-2a36-4e3f-b6e9-1e03cc051518

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) : (0 : ℝ) < (l : ℝ) - 1 := by
  have : (2 : ℝ) ≤ l := by exact_mod_cast hl
  linarith
end GlobalTheory.RadiiIdentities
