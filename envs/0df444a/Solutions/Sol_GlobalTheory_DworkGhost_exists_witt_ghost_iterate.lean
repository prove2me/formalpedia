-- Prove2me | solution 1 for GlobalTheory.DworkGhost.exists_witt_ghost_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:17.134046+00:00
-- url     : https://prove2.me/submissions/2e867d05-1ebc-4900-9165-34879a412eaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate
import Theorems.Thm_GlobalTheory_DworkGhost_ghost_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Finset
open GlobalTheory GlobalTheory.DworkGhost
namespace GlobalTheory.DworkGhost
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]
  rfl
end GlobalTheory.DworkGhost
