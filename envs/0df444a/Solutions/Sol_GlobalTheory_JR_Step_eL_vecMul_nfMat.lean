-- Prove2me | solution 1 for GlobalTheory.JR.Step.eL_vecMul_nfMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:14.898789+00:00
-- url     : https://prove2.me/submissions/67e1f26d-3751-4684-9799-bd86ba9fa8a8

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
namespace GlobalTheory.JR.Step
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]
end GlobalTheory.JR.Step
