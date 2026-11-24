-- Prove2me | solution 1 for GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:27.034624+00:00
-- url     : https://prove2.me/submissions/c7d9332b-e63a-4a41-bc45-2673601c67bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpaceStatement
import Theorems.Thm_GlobalTheory_WeilCriterion_modulusClause


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ModulusClause := by
  first | exact @GlobalTheory.WeilCriterion.modulusClause | exact GlobalTheory.WeilCriterion.modulusClause | (intros; apply GlobalTheory.WeilCriterion.modulusClause <;> assumption)
end _root_.GlobalTheory.T
