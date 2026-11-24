-- Prove2me | solution 1 for GlobalTheory.T.character_annihilator_integer_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:36.947425+00:00
-- url     : https://prove2.me/submissions/e11ad16a-f975-49f2-bf83-153f1a6bff03

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLatticeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_isCompact_isOpen_annihilator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 → IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧ IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | exact GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | (intros; apply GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator <;> assumption)
end _root_.GlobalTheory.T
