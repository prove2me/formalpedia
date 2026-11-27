-- Prove2me | solution 1 for GlobalTheory.UnitaryLog.lie_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:47.994135+00:00
-- url     : https://prove2.me/submissions/eef8fbdf-0ba6-4e90-9ead-018f2d72dbea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace GlobalTheory.UnitaryLog
theorem _root_.solution {n : ℕ} (U : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : X = -(((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
      (U : Matrix (Fin n) (Fin n) ℂ))) : Xᴴ * (U : Matrix (Fin n) (Fin n) ℂ) + (U : Matrix (Fin n) (Fin n) ℂ) * X = 0 := by
  have e : (U : Matrix (Fin n) (Fin n) ℂ) * X = -(Xᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) := by
    conv_lhs => rw [h]
    rw [mul_neg, mul_assoc (((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)),
      Units.mul_inv_cancel_left]
  rw [e, add_neg_cancel]
end GlobalTheory.UnitaryLog
