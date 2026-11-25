-- Prove2me | solution 1 for GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:23:23.074846+00:00
-- url     : https://prove2.me/submissions/12bc557c-a8c5-4d9b-a64f-f7fcf9238b5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PreimageDiagOneGeneralLinearEmbeddingIntegralGLSStatement
import Theorems.Thm_GlobalTheory_JR_GLift_emb_preimage_glO


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] (r : ℕ), ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  first | exact @GlobalTheory.JR.GLift.emb_preimage_glO | exact GlobalTheory.JR.GLift.emb_preimage_glO | (intros; apply GlobalTheory.JR.GLift.emb_preimage_glO <;> assumption)
end _root_.GlobalTheory.T
