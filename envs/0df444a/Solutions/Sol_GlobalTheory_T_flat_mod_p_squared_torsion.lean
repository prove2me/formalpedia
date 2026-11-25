-- Prove2me | solution 1 for GlobalTheory.T.flat_mod_p_squared_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:06.63058+00:00
-- url     : https://prove2.me/submissions/7364c97c-132c-4ffe-a683-1291e1d0790c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatModPSquaredTorsion
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FlatModPSquaredTorsion
import Theorems.Thm_GlobalTheory_flat_zmod_sq_mul_p_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  first | exact @_root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | exact _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | (intros; apply _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff <;> assumption)
end _root_.GlobalTheory.T
