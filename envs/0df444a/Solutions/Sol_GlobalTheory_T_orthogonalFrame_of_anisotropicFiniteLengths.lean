-- Prove2me | solution 1 for GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:37.255301+00:00
-- url     : https://prove2.me/submissions/c5c3a1b9-939f-49f8-93b8-e55219da747c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalFrameOfAnisotropicFiniteLengths
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalFrameOfAnisotropicFiniteLengthsStatement
import Theorems.Thm_GlobalTheory_SmoothForms_orthoSmall_of_anisoSmall


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], AnisoSmall E → OrthoSmall E := by
  first | exact @GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | exact GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | (intros; apply GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall <;> assumption)
end _root_.GlobalTheory.T
