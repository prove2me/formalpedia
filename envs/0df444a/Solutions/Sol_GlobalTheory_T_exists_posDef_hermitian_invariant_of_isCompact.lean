-- Prove2me | solution 1 for GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:26:40.090064+00:00
-- url     : https://prove2.me/submissions/72f7ae6b-171e-416d-92fd-edd51c5a9a95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantPosDefHermitian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantPosDefHermitianStatement
import Theorems.Thm_GlobalTheory_CompactAvg_exists_invariant_posDef_hermitian


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
theorem _root_.solution : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  first | exact @GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | exact GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | (intros; apply GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian <;> assumption)
end _root_.GlobalTheory.T
