-- Prove2me | solution 1 for GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:08.104246+00:00
-- url     : https://prove2.me/submissions/3f197ad9-7001-44f0-8ec5-dedfd4644fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GhostComponentInjectiveOfNoTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GhostComponentInjectiveOfNoTorsionStatement
import Theorems.Thm_GlobalTheory_WittVector_ghostComponent_injective_of_noTorsion


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
end _root_.GlobalTheory.T
