-- Prove2me | solution 1 for GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:48.665186+00:00
-- url     : https://prove2.me/submissions/d1d8397e-3f84-4ddd-afbc-8244c0d95839

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
import Theorems.Thm_GlobalTheory_JR_Step_nfMat_mulVec_castSucc

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
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [nfMat, Matrix.mulVec, dotProduct, eL]
  | cast i =>
    rw [nfMat_mulVec_castSucc]
    simp [eL, Pi.single_apply, Fin.castSucc_ne_last]
end GlobalTheory.JR.Step
