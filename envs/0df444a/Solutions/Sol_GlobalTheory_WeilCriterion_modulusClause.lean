-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.modulusClause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:12.513456+00:00
-- url     : https://prove2.me/submissions/3b973e3e-d504-4052-9779-4b783c841cb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_exists_isInvariantRadon
import Theorems.Thm_GlobalTheory_WeilCriterion_isInvariantRadon_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
namespace GlobalTheory.WeilCriterion
theorem _root_.solution : ModulusClause := by
  intro G _ _ _ _ _ _ H _ _ _ hH hΔ
  borelize G
  exact ⟨exists_isInvariantRadon H hH hΔ, isInvariantRadon_unique H hH⟩
end GlobalTheory.WeilCriterion
