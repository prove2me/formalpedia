-- Prove2me | solution 1 for GlobalTheory.T.levi_quotient_of_block_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:21.550621+00:00
-- url     : https://prove2.me/submissions/5b5a714d-2ffe-4348-9e2c-80952c46e1d9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_leviQ


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
theorem _root_.solution : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | exact GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ | (intros; apply GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ <;> assumption)
end _root_.GlobalTheory.T
