-- Prove2me | solution 1 for GlobalTheory.T.reduced_artinian_involution_idempotent_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:03.38816+00:00
-- url     : https://prove2.me/submissions/acd62408-30d6-4cff-930d-2635f79dd5f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReducedArtinianInvolutionIdempotentSplitStatement
import Theorems.Thm_GlobalTheory_reducedArtinian_involution_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧ ∀ w, w * σ w = 0 → w * f = 0 := by
  first | exact @GlobalTheory.reducedArtinian_involution_split | exact GlobalTheory.reducedArtinian_involution_split | (intros; apply GlobalTheory.reducedArtinian_involution_split <;> assumption)
end _root_.GlobalTheory.T
