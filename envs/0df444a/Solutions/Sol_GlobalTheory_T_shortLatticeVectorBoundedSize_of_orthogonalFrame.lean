-- Prove2me | solution 1 for GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:22.040814+00:00
-- url     : https://prove2.me/submissions/0f32021c-a51e-4da2-82b0-8ff7fcd455e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrameStatement
import Theorems.Thm_GlobalTheory_SmoothForms_Short_shortSmall


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E → ShortSmall E := by
  first | exact @GlobalTheory.SmoothForms.Short.shortSmall | exact GlobalTheory.SmoothForms.Short.shortSmall | (intros; apply GlobalTheory.SmoothForms.Short.shortSmall <;> assumption)
end _root_.GlobalTheory.T
