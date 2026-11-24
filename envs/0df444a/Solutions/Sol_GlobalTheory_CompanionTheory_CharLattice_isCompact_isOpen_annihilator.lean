-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:15.785097+00:00
-- url     : https://prove2.me/submissions/9260ea2f-4117-43f7-9b37-a789303acd0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
import Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_isOpen_annihilator
import Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_isClosed_annihilator
import Theorems.Thm_GlobalTheory_CompanionTheory_CharLattice_annihilator_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharLattice
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 →
      IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧
      IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  intro k _ _ _ _ ψ hψ hne n b hb
  have e : {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} =
      (annihilator ψ n b : Set (Fin n → k)) := rfl
  rw [e]
  obtain ⟨y₀, hy⟩ : ∃ y₀, ψ y₀ ≠ 1 := by
    by_contra h
    exact hne (AddChar.ext ψ 1 fun y => by
      rw [AddChar.one_apply]
      by_contra hy
      exact h ⟨y, hy⟩)
  refine ⟨?_, isOpen_annihilator ψ hψ n b hb⟩
  exact (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _).of_isClosed_subset
    (isClosed_annihilator ψ hψ n b) (annihilator_subset ψ n b hb y₀ hy)
end GlobalTheory.CompanionTheory.CharLattice
