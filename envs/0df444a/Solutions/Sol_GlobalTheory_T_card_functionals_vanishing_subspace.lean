-- Prove2me | solution 1 for GlobalTheory.T.card_functionals_vanishing_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:12.4443+00:00
-- url     : https://prove2.me/submissions/0e5ea8c9-e9c6-4898-b679-130e686df2ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspace
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_card_forms_vanishing_missing_line


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
  Module.finrank k M + (j + 1) = n + 1 →
  (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | exact GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line <;> assumption)
end _root_.GlobalTheory.T
