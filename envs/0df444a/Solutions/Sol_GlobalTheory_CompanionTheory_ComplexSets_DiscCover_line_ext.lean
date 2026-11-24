-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.line_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:32.731939+00:00
-- url     : https://prove2.me/submissions/58ccad99-7e52-4a5d-b6c5-ec7d97bc0a43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward

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
theorem _root_.solution {y y' : Fin 1 → ℂ} (h : y 0 = y' 0) : y = y' := by
  funext i
  rw [Subsingleton.elim i 0]
  exact h
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
