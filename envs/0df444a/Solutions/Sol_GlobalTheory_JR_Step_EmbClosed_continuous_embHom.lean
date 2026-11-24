-- Prove2me | solution 1 for GlobalTheory.JR.Step.EmbClosed.continuous_embHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:38.340569+00:00
-- url     : https://prove2.me/submissions/13d79a65-f6fa-48c5-9823-41d595d7f38c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneGeneralLinearEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.EmbClosed
namespace GlobalTheory.JR.Step.EmbClosed
theorem _root_.solution (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _
end GlobalTheory.JR.Step.EmbClosed
