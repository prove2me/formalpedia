-- Prove2me | solution 1 for GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:17.102803+00:00
-- url     : https://prove2.me/submissions/e935be58-80c4-48e1-b2e5-287f64e4332f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientInvariantMeasureExistsUniqueUnimodular
import Theorems.Thm_GlobalTheory_Proof_quotientInvariantMeasure_exists_unique_unimodular_modularCharacter_eq_one
import Theorems.Thm_GlobalTheory_T_weil_criterion_invariant_measure_homogeneous_space


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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
theorem _root_.solution : InvariantMeasureClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH uG uH
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH fun h => ?_
  rw [modularCharacter_eq_one uG, modularCharacter_eq_one uH]
end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
