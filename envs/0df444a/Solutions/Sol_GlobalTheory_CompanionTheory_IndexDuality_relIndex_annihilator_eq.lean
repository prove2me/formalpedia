-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:18.914695+00:00
-- url     : https://prove2.me/submissions/e77cd442-2ddc-4c84-9474-31f0c286bf5f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDuality
import Theorems.Thm_GlobalTheory_CompanionTheory_IndexDuality_relIndex_le_of_pairing
import Theorems.Thm_GlobalTheory_CompanionTheory_CharacterBiduality_exists_annihilator_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_RelIndex_relIndex_ne_zero_of_isCompact_of_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IndexDuality
namespace GlobalTheory.CompanionTheory.IndexDuality
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) →
    IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) →
    (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  intro k _ _ _ _ ψ hψc hψ1 n A₀ A P₀ P hA₀c hA₀o hAc hAo hle hP₀ hP
  have hfin : A₀.relIndex A ≠ 0 :=
    GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen A A₀ hAc hA₀o hle
  have h1 := relIndex_le_of_pairing (fun ξ a : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun ξ ξ' a => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    (fun ξ a a' => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    A₀ A P₀ P hfin (fun ξ hξ a ha => (hP₀ ξ).mp hξ a ha) (fun ξ _ h => (hP ξ).mpr h)
  have h2 := relIndex_le_of_pairing (fun a ξ : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun a a' ξ => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    (fun a ξ ξ' => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    P P₀ A A₀ h1.1 (fun a _ ξ hξ => (hP ξ).mp hξ a ‹_›) (fun a _ h => by
      by_contra hna
      obtain ⟨η, hη, hne⟩ := GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne k ψ hψc hψ1 n A₀ hA₀c hA₀o a hna
      exact hne (h η ((hP₀ η).mpr hη)))
  exact le_antisymm h1.2 h2.2
end GlobalTheory.CompanionTheory.IndexDuality
