-- Prove2me | solution 1 for GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:43.198307+00:00
-- url     : https://prove2.me/submissions/ff175f96-6db3-4527-8b85-a8f669740355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLowering
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLoweringStatement
import Theorems.Thm_GlobalTheory_WigSh_inv_sq_le_wM


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
theorem _root_.solution : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wM | exact GlobalTheory.WigSh.inv_sq_le_wM | (intros; apply GlobalTheory.WigSh.inv_sq_le_wM <;> assumption)
end _root_.GlobalTheory.T
