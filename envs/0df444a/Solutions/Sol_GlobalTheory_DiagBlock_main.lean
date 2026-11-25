-- Prove2me | solution 1 for GlobalTheory.DiagBlock.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:27.056267+00:00
-- url     : https://prove2.me/submissions/3c35ed99-6ffc-4e70-9fc0-e6f4347d0d33

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_restrictMul
import Theorems.Thm_GlobalTheory_DiagBlock_restrictExp
import Theorems.Thm_GlobalTheory_DiagBlock_detPowDiag
import Theorems.Thm_GlobalTheory_DiagBlock_blockJet

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
theorem _root_.solution : DetPowDiag ∧ BlockJet ∧ RestrictMul ∧ RestrictExp := ⟨detPowDiag, blockJet, restrictMul, restrictExp⟩
end GlobalTheory.DiagBlock
