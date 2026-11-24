-- Prove2me | solution 1 for GlobalTheory.T.doubledLattice_primitive_isotropic_frame_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:41.451836+00:00
-- url     : https://prove2.me/submissions/d8387a0a-1c7c-47a4-9dd1-b6d3e80fc2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletionStatement
import Theorems.Thm_GlobalTheory_FrameCompletion_completion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Completion := by
  first | exact @GlobalTheory.FrameCompletion.completion | exact GlobalTheory.FrameCompletion.completion | (intros; apply GlobalTheory.FrameCompletion.completion <;> assumption)
end _root_.GlobalTheory.T
