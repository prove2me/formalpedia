-- Prove2me | solution 1 for GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:06.948888+00:00
-- url     : https://prove2.me/submissions/49aa7855-505c-4a2c-b54d-c8a672c00bd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_tm_isClosedEmbedding


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  first | exact @GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | exact GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | (intros; apply GlobalTheory.JR.LinDesc.tm_isClosedEmbedding <;> assumption)
end _root_.GlobalTheory.T
