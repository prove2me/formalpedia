-- Prove2me | solution 1 for GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:29.711294+00:00
-- url     : https://prove2.me/submissions/f4d07299-d940-49a4-b794-66b9aeac4818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneGeneralLinearEmbedding
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneGeneralLinearEmbeddingStatement
import Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_isClosedEmbedding_emb


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
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
end _root_.GlobalTheory.T
