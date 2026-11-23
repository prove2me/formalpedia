-- Prove2me | solution 1 for GlobalTheory.JR.Step.nfMat_mulVec_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:49.667812+00:00
-- url     : https://prove2.me/submissions/06c6c65b-5884-47b8-8f65-13fb30415297

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
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by
  simp only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [h]
  · simp
end GlobalTheory.JR.Step
