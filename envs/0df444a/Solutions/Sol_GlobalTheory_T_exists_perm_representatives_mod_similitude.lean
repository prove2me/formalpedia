-- Prove2me | solution 1 for GlobalTheory.T.exists_perm_representatives_mod_similitude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:00.851813+00:00
-- url     : https://prove2.me/submissions/08145da6-285f-49e4-92d9-3ad46a541446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTransposeStatement
import Theorems.Thm_GlobalTheory_exists_representatives_mod_similitude_transpose


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
theorem _root_.solution : ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  first | exact @GlobalTheory.exists_representatives_mod_similitude_transpose | exact GlobalTheory.exists_representatives_mod_similitude_transpose | (intros; apply GlobalTheory.exists_representatives_mod_similitude_transpose <;> assumption)
end _root_.GlobalTheory.T
