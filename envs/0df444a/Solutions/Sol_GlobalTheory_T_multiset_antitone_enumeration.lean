-- Prove2me | solution 1 for GlobalTheory.T.multiset_antitone_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:33.186802+00:00
-- url     : https://prove2.me/submissions/219878fd-53b4-474b-8ff2-565b70b80874

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumeration
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumerationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Multiset_exists_antitone_listing


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
theorem _root_.solution : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  first | exact @GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | exact GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | (intros; apply GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing <;> assumption)
end _root_.GlobalTheory.T
