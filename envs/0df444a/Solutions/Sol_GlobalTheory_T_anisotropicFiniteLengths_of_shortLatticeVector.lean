-- Prove2me | solution 1 for GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:42.192012+00:00
-- url     : https://prove2.me/submissions/5eb31b0d-890a-42d7-8536-87f11a5caf21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVectorStatement
import Theorems.Thm_GlobalTheory_AnisoSize_anisoSmall_of_shortSmall


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ShortSmall E → AnisoSmall E := by
  first | exact @GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | exact GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | (intros; apply GlobalTheory.AnisoSize.anisoSmall_of_shortSmall <;> assumption)
end _root_.GlobalTheory.T
