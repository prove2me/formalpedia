-- Prove2me | solution 1 for GlobalTheory.UnitaryLog.exp_conj_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:42.259008+00:00
-- url     : https://prove2.me/submissions/4207aee0-a1b3-4fab-8fa3-926406ec49ca

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
theorem _root_.solution {n : ℕ} (U : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X u : Matrix (Fin n) (Fin n) ℂ)
    (hX : NormedSpace.exp X = u) (hu : uᴴ * (U : Matrix (Fin n) (Fin n) ℂ) * u = U) :
    NormedSpace.exp (-(((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
      (U : Matrix (Fin n) (Fin n) ℂ))) = u := by
  rw [Matrix.exp_neg, Matrix.exp_units_conj', Matrix.exp_conjTranspose, hX]
  apply Matrix.inv_eq_right_inv
  rw [mul_assoc, mul_assoc, ← mul_assoc uᴴ, hu, Units.inv_mul]
end GlobalTheory.UnitaryLog
