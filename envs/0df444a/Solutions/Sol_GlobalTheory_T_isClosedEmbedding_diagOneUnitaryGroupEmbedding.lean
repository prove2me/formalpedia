-- Prove2me | solution 1 for GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:32.429157+00:00
-- url     : https://prove2.me/submissions/4658634e-55c5-4b33-96d0-58b211454305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneUnitaryGroupEmbeddingStatement
import Theorems.Thm_GlobalTheory_JR_Step_isClosedEmbedding_uEmb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  first | exact @GlobalTheory.JR.Step.isClosedEmbedding_uEmb | exact GlobalTheory.JR.Step.isClosedEmbedding_uEmb | (intros; apply GlobalTheory.JR.Step.isClosedEmbedding_uEmb <;> assumption)
end _root_.GlobalTheory.T
