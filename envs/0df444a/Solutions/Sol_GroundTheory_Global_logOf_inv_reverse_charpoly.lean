-- Prove2me | solution 1 for GroundTheory.Global.logOf_inv_reverse_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:06.223939+00:00
-- url     : https://prove2.me/submissions/b001a262-4286-4d41-8c0d-b7c12abaa304

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Theorems.Thm_GroundTheory_Global_mul_derivative_logOf
import Theorems.Thm_GroundTheory_Global_constantCoeff_reverse_charpoly
import Theorems.Thm_GroundTheory_Global_coe_derivative_reverse_charpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
namespace GroundTheory.Global
theorem _root_.solution [CharZero k] (A : Module.End k W) :
    PowerSeries.logOf ((A.charpoly.reverse : PowerSeries k)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else LinearMap.trace k W (A ^ m) / m := by
  set P : PowerSeries k := ((A.charpoly.reverse : k[X]) : PowerSeries k) with hPdef
  set D : PowerSeries k := PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1))
  have hP : PowerSeries.constantCoeff P = 1 := constantCoeff_reverse_charpoly A
  have hPinv : PowerSeries.constantCoeff P⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hP, inv_one]
  have hPP : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel P (by rw [hP]; exact one_ne_zero)
  have hdP : PowerSeries.derivative k P = -P * D := by
    rw [hPdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
  have key := mul_derivative_logOf P⁻¹ hPinv
  rw [PowerSeries.derivative_inv', hdP] at key
  apply PowerSeries.derivative.ext
  · have hD : PowerSeries.derivative k (PowerSeries.mk fun m =>
        if m = 0 then 0 else LinearMap.trace k W (A ^ m) / m) = D := by
      ext n
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg n.succ_ne_zero,
        Nat.cast_add_one, div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)]
    rw [hD]
    calc PowerSeries.derivative k (PowerSeries.logOf P⁻¹)
        = P * (P⁻¹ * PowerSeries.derivative k (PowerSeries.logOf P⁻¹)) := by
          rw [← mul_assoc, hPP, one_mul]
      _ = P * (P⁻¹ * D * (P * P⁻¹)) := by rw [key]; ring
      _ = D := by rw [hPP, mul_one, ← mul_assoc, hPP, one_mul]
  · rw [PowerSeries.constantCoeff_logOf hPinv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, if_pos rfl]
end GroundTheory.Global
