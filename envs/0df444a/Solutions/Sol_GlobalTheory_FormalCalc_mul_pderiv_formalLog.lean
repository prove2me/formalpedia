-- Prove2me | solution 1 for GlobalTheory.FormalCalc.mul_pderiv_formalLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:15.101513+00:00
-- url     : https://prove2.me/submissions/2d871157-dbe5-4128-8516-be6b23936765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_powerSeries_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    PowerSeries.HasSubst (g - 1) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hg])
private theorem one_add_X_mul_deriv_log :
    (1 + PowerSeries.X) * PowerSeries.derivative A (PowerSeries.log A) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ]
end GlobalTheory.FormalCalc
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) (i : σ) :
    g * pderiv A i (formalLog g) = pderiv A i g := by
  have hs := hasSubst_sub_one hg
  have h := congrArg (PowerSeries.substAlgHom (R := A) hs) (one_add_X_mul_deriv_log (A := A))
  rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel,
    PowerSeries.coe_substAlgHom] at h
  rw [formalLog, pderiv_powerSeries_subst hs, ← mul_assoc, h, map_sub, pderiv_one, sub_zero,
    one_mul]
end GlobalTheory.FormalCalc
