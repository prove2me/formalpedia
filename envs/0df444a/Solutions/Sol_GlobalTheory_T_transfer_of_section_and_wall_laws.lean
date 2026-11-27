-- Prove2me | solution 1 for GlobalTheory.T.transfer_of_section_and_wall_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:32.511437+00:00
-- url     : https://prove2.me/submissions/4fc5c4d2-a50f-4723-b5b2-63f24df728b2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TransferOfSectionAndWallLaws
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TransferOfSectionAndWallLawsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_transfer


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
theorem _root_.solution : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgTransfer.transfer | exact GlobalTheory.CompanionTheory.RgTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgTransfer.transfer <;> assumption)
end _root_.GlobalTheory.T
