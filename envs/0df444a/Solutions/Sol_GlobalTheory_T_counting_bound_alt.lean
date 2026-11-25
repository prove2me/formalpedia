-- Prove2me | solution 1 for GlobalTheory.T.counting_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:02.480496+00:00
-- url     : https://prove2.me/submissions/affebd9f-454e-41cd-884b-c3dce2a367b9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMulStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MassCount_countBd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : CountBd := by
  first | exact @GlobalTheory.CompanionTheory.MassCount.countBd | exact GlobalTheory.CompanionTheory.MassCount.countBd | (intros; apply GlobalTheory.CompanionTheory.MassCount.countBd <;> assumption)
end _root_.GlobalTheory.T
