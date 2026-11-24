-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:12.724064+00:00
-- url     : https://prove2.me/submissions/7a7a1a46-afe3-4736-8c9f-5ab8c5081696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
end GlobalTheory.JR.LinDesc
