-- Prove2me | solution 1 for GlobalTheory.T.smooth_range_of_idempotent_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:39.986994+00:00
-- url     : https://prove2.me/submissions/ffd7b5f5-cafa-4928-88bb-8fc40e380ebf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHomStatement
import Theorems.Thm_GlobalTheory_smooth_range_of_idempotent


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
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  first | exact @GlobalTheory.smooth_range_of_idempotent | exact GlobalTheory.smooth_range_of_idempotent | (intros; apply GlobalTheory.smooth_range_of_idempotent <;> assumption)
end _root_.GlobalTheory.T
