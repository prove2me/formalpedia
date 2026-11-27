-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.eq_smul_haarGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:30.585159+00:00
-- url     : https://prove2.me/submissions/dbc6c4f5-ce2c-451d-a292-0c3760b2d585

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable (μ₀ : Measure (Fin n × Fin n → F)) [μ₀.IsAddHaarMeasure]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ = haarScalarFactor μ (haarGL F n μ₀) • haarGL F n μ₀ :=
  isMulLeftInvariant_eq_smul μ _
end GroundTheory.Automorphic.Measures
