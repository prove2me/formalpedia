-- Prove2me | solution 1 for GlobalTheory.DiagBlock.restrictMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:31.221237+00:00
-- url     : https://prove2.me/submissions/ad836c73-ff79-4320-808c-18c19cf80a18

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_restr_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution : RestrictMul := by
  intro C _ n0 n hn G G'
  rw [restr_eq, restr_eq, restr_eq, map_mul]
end GlobalTheory.DiagBlock
