-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.line_dist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:10.992856+00:00
-- url     : https://prove2.me/submissions/636fbec0-a35b-4c92-99c4-70b5e3de3aa4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_const_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric
namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover
theorem _root_.solution (y y' : Fin 1 → ℂ) : dist y y' = dist (y 0) (y' 0) := by
  have h : dist (fun _ : Fin 1 => y 0) (fun _ : Fin 1 => y' 0) = dist (y 0) (y' 0) :=
    dist_pi_const (y 0) (y' 0)
  rw [const_coord y, const_coord y'] at h
  exact h
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
