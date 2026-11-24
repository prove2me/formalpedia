-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:40.768845+00:00
-- url     : https://prove2.me/submissions/43eac504-49e6-44b8-a28c-542b1a1a1064

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre_split
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  intro E _ τ q ε h t ht t0
  have hq := h.one_lt
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hnf⟩
  · rw [card_fibre_field h hf ht t0]
    omega
  · rw [card_fibre_split h hnf ht t0]
    omega
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
