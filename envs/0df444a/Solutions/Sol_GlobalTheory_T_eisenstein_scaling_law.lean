-- Prove2me | solution 1 for GlobalTheory.T.eisenstein_scaling_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:09.234249+00:00
-- url     : https://prove2.me/submissions/06c16eba-a9e3-436a-ae06-6c59544b17fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLaw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLawStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisScale_scale


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
theorem _root_.solution : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
end _root_.GlobalTheory.T
