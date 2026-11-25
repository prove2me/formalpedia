-- Prove2me | solution 1 for GlobalTheory.T.isPullback_whiskerLeft_left_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:50:40.071194+00:00
-- url     : https://prove2.me/submissions/3543051e-b1ff-4429-b513-3836476a0da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSndStatement
import Theorems.Thm_GlobalTheory_whiskerLeft_left_isPullback_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  first | exact @GlobalTheory.whiskerLeft_left_isPullback_snd | exact GlobalTheory.whiskerLeft_left_isPullback_snd | (intros; apply GlobalTheory.whiskerLeft_left_isPullback_snd <;> assumption)
end _root_.GlobalTheory.T
