-- Prove2me | solution 1 for GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_embHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:47.295784+00:00
-- url     : https://prove2.me/submissions/1c6e131d-c5d4-4b50-b8b4-1523f66ac02b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneGeneralLinearEmbedding
import Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_embHom_castSucc
import Theorems.Thm_GlobalTheory_JR_Step_EmbClosed_continuous_embHom

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
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)
end GlobalTheory.JR.Step.EmbClosed
