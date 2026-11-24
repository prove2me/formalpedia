-- Prove2me | solution 1 for GlobalTheory.T.exists_invariant_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:10:07.566207+00:00
-- url     : https://prove2.me/submissions/d084d0a2-05ee-4da3-b0de-ea323c4d7027

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantRightInverseOfRightInverse
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantRightInverseOfRightInverseStatement
import Theorems.Thm_GlobalTheory_invariant_right_inverse_of_right_inverse


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
theorem _root_.solution : ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) → ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first | exact @GlobalTheory.invariant_right_inverse_of_right_inverse | exact GlobalTheory.invariant_right_inverse_of_right_inverse | (intros; apply GlobalTheory.invariant_right_inverse_of_right_inverse <;> assumption)
end _root_.GlobalTheory.T
