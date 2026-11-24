-- Prove2me | solution 1 for GlobalTheory.invariant_right_inverse_of_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:51.101687+00:00
-- url     : https://prove2.me/submissions/24b62b22-6609-4782-8263-f77823b77f9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantRightInverseField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantRightInverseOfRightInverse
import Theorems.Thm_GlobalTheory_InvariantRightInverse_exists_invariant_rightInverse


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)
end GlobalTheory
