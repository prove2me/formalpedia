-- Prove2me | solution 1 for GroundTheory.LocalField.Padic.not_isTrivialOn_stdChar_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:54.237774+00:00
-- url     : https://prove2.me/submissions/1f84c2b6-a106-48f3-aaaa-b4c2f3125a65

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Theorems.Thm_GroundTheory_LocalField_Padic_ord_p
import Theorems.Thm_GroundTheory_LocalField_Padic_stdChar_inv_p_ne_one

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
theorem _root_.solution : ¬ IsTrivialOn (stdChar p) (-1) := by
  intro h
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply stdChar_inv_p_ne_one p
  apply h
  rw [mem_valBall_iff_le_ord (inv_ne_zero hpp), ord_inv hpp, ord_p]
end GroundTheory.LocalField.Padic
