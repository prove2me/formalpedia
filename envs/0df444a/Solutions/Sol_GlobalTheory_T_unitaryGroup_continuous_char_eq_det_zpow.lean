-- Prove2me | solution 1 for GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:50.459931+00:00
-- url     : https://prove2.me/submissions/797f705f-42ac-496c-a95b-46a1ed145349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Theorems.Thm_GlobalTheory_UnitaryChar_char_eq_det_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  first | exact @GlobalTheory.UnitaryChar.char_eq_det_zpow | exact GlobalTheory.UnitaryChar.char_eq_det_zpow | (intros; apply GlobalTheory.UnitaryChar.char_eq_det_zpow <;> assumption)
end _root_.GlobalTheory.T
