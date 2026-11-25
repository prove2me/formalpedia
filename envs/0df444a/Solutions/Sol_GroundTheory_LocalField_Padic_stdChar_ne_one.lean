-- Prove2me | solution 1 for GroundTheory.LocalField.Padic.stdChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:34.861167+00:00
-- url     : https://prove2.me/submissions/0fc39977-4aa5-403b-9a87-8194a7cf603d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Theorems.Thm_GroundTheory_LocalField_Padic_not_isTrivialOn_stdChar_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
namespace GroundTheory.LocalField.Padic
theorem _root_.solution : stdChar p ≠ 1 := by
  intro h
  apply not_isTrivialOn_stdChar_neg_one p
  rw [h]
  intro x _
  exact AddChar.one_apply x
end GroundTheory.LocalField.Padic
