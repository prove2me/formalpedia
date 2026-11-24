-- Prove2me | solution 1 for GlobalTheory.JR.MatchAdd.integrable_of_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:01:07.178936+00:00
-- url     : https://prove2.me/submissions/b6e24771-bcf9-41b2-a2ed-eb759ebf526d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.MatchAdd
theorem _root_.solution {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2
end GlobalTheory.JR.MatchAdd
