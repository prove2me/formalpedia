-- Prove2me | solution 1 for GlobalTheory.T.isOpen_character_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:02.352437+00:00
-- url     : https://prove2.me/submissions/357ae3fb-a144-4b83-a405-eab3e6bef9d9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilator
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilatorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AnnihOpen_isOpen_annihilator_of_isCompact


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
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | exact GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact <;> assumption)
end _root_.GlobalTheory.T
