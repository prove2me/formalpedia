-- Prove2me | solution 1 for GlobalTheory.BasisLeftInverse.exists_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:23.652793+00:00
-- url     : https://prove2.me/submissions/5bd1509f-7059-4d17-b274-d3ec0f904a75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InjectiveMulVecMapBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BasisLeftInverse
namespace GlobalTheory.BasisLeftInverse
theorem _root_.solution {E : Type} [Field E] {n d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (h : LinearIndependent E B.col) : ∃ C : Matrix (Fin d) (Fin n) E, C * B = 1 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
end GlobalTheory.BasisLeftInverse
