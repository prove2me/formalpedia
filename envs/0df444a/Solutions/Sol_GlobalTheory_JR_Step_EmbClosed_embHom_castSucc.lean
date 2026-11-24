-- Prove2me | solution 1 for GlobalTheory.JR.Step.EmbClosed.embHom_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:39.07441+00:00
-- url     : https://prove2.me/submissions/b546a2bf-5a7a-4275-966b-d8d55a6ca315

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
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]
end GlobalTheory.JR.Step.EmbClosed
