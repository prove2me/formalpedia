-- Prove2me | solution 1 for GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:02.347844+00:00
-- url     : https://prove2.me/submissions/2e6546a1-62fb-4552-b4a7-72abe19abe87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterateStatement
import Theorems.Thm_GlobalTheory_DworkGhost_exists_witt_ghost_iterate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
end _root_.GlobalTheory.T
