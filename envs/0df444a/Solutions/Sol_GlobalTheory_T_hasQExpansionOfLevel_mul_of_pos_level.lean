-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:27.398163+00:00
-- url     : https://prove2.me/submissions/ec865a15-fbd0-40cd-b808-3da79d303d0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevelStatement
import Theorems.Thm_GlobalTheory_QFam_hasQ_mul_conv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ * g τ) (conv a b) := by
  first | exact @GlobalTheory.QFam.hasQ_mul_conv | exact GlobalTheory.QFam.hasQ_mul_conv | (intros; apply GlobalTheory.QFam.hasQ_mul_conv <;> assumption)
end _root_.GlobalTheory.T
