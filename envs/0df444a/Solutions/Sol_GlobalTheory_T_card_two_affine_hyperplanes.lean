-- Prove2me | solution 1 for GlobalTheory.T.card_two_affine_hyperplanes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:17.214169+00:00
-- url     : https://prove2.me/submissions/61249305-d491-4814-a00a-d414d6b61144

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_card_two_equations


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
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k), a ≠ 0 → (∀ s : k, b ≠ s • a) →
  Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | exact GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_two_equations <;> assumption)
end _root_.GlobalTheory.T
