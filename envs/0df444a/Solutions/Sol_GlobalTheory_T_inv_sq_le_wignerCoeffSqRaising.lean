-- Prove2me | solution 1 for GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:22:58.804947+00:00
-- url     : https://prove2.me/submissions/b4fc5123-eed0-4a63-a3e2-5c831c66c698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaising
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaisingStatement
import Theorems.Thm_GlobalTheory_WigSh_inv_sq_le_wP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l + 1) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wP L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wP | exact GlobalTheory.WigSh.inv_sq_le_wP | (intros; apply GlobalTheory.WigSh.inv_sq_le_wP <;> assumption)
end _root_.GlobalTheory.T
