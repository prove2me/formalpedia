-- Prove2me | solution 1 for GlobalTheory.T.exists_character_separating_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:40.592585+00:00
-- url     : https://prove2.me/submissions/a6f6f54d-85b5-49a1-a8bb-341e9dbac6e7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLatticeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CharacterBiduality_exists_annihilator_ne


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
end _root_.GlobalTheory.T
