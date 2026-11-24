-- Prove2me | solution 1 for GlobalTheory.BK.mxInv_rankOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:50:14.775039+00:00
-- url     : https://prove2.me/submissions/102d4fee-ccee-4e3e-a952-fd3791530901

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_Ezpow_neg_mul
import Theorems.Thm_GlobalTheory_BK_mx_rankOne_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
namespace GlobalTheory.BK
theorem _root_.solution (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mxInv τ i k = Ezpow K l e (-j τ) := by
  have h := congrFun (congrFun ((rankOne O K l e j).mxInv_mul_mx τ) ()) ()
  rw [Matrix.mul_apply, Fintype.sum_unique, mx_rankOne_eq, Matrix.one_apply_eq,
    ← Ezpow_neg_mul l e (j τ)] at h
  exact mul_right_cancel₀ (Units.ne_zero _) h
end GlobalTheory.BK
