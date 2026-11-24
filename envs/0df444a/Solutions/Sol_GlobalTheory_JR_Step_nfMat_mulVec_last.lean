-- Prove2me | solution 1 for GlobalTheory.JR.Step.nfMat_mulVec_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:46.016795+00:00
-- url     : https://prove2.me/submissions/7185c2bb-6829-4692-84f3-00e9f81f0db7

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
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]
end GlobalTheory.JR.Step
