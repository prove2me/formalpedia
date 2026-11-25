-- Prove2me | solution 1 for GlobalTheory.T.exists_skewHermitian_log_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:35.646813+00:00
-- url     : https://prove2.me/submissions/a69b7f87-4ab2-4fc5-89b8-7c65e97c1412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryExistsSkewLog
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryExistsSkewLogStatement
import Theorems.Thm_GlobalTheory_unitary_exists_skew_log


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
theorem _root_.solution : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  first | exact @GlobalTheory.unitary_exists_skew_log | exact GlobalTheory.unitary_exists_skew_log | (intros; apply GlobalTheory.unitary_exists_skew_log <;> assumption)
end _root_.GlobalTheory.T
