-- Prove2me | solution 1 for GlobalTheory.T.card_coset_reps_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:46.656603+00:00
-- url     : https://prove2.me/submissions/d67ebe5e-ee29-4789-9084-0fbf3c1d24eb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardCosetRepsEqRelIndex
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardCosetRepsEqRelIndexStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Transversal_card_eq_relIndex


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X), L ≤ A → (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) → T.card = L.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | exact GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | (intros; apply GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex <;> assumption)
end _root_.GlobalTheory.T
