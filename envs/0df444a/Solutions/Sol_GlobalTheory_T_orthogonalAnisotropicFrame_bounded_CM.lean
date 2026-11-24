-- Prove2me | solution 1 for GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:56.28233+00:00
-- url     : https://prove2.me/submissions/cd108adb-1af4-46ad-b8bb-68aab42a7d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCMStatement
import Theorems.Thm_GlobalTheory_SmoothForms_frameSmall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  first | exact @GlobalTheory.SmoothForms.frameSmall | exact GlobalTheory.SmoothForms.frameSmall | (intros; apply GlobalTheory.SmoothForms.frameSmall <;> assumption)
end _root_.GlobalTheory.T
