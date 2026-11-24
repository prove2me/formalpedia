-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartz_bump_near_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:09.395241+00:00
-- url     : https://prove2.me/submissions/392b6d83-69e7-448b-b99b-6ce97ed4c73f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_exists_test


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)), IsOpen S → (1 : GL (Fin r) k) ∈ S →
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by
  first | exact @GlobalTheory.GodementJacquet.TestNearE.exists_test | exact GlobalTheory.GodementJacquet.TestNearE.exists_test | (intros; apply GlobalTheory.GodementJacquet.TestNearE.exists_test <;> assumption)
end _root_.GlobalTheory.T
