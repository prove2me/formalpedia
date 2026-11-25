-- Prove2me | solution 1 for GlobalTheory.T.meet_over_hypersurface_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:29.466609+00:00
-- url     : https://prove2.me/submissions/657c3309-d39b-491a-8dd9-65f8ef3f5e40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGermStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : FiniteFibreGermIntegral.Statement → IrreducibleGermMeetOverHypersurface.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral <;> assumption)
end _root_.GlobalTheory.T
