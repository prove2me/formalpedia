-- Prove2me | solution 1 for GlobalTheory.T.dominant_components_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:15.117381+00:00
-- url     : https://prove2.me/submissions/95438439-125c-42fe-a5be-5bb81766365b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGermStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_openProjectionDominantComponents_of_analyticGermComponents


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
theorem _root_.solution : AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | exact GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents <;> assumption)
end _root_.GlobalTheory.T
