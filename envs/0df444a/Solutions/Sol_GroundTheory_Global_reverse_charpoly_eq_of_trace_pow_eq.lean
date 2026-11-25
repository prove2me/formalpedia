-- Prove2me | solution 1 for GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:07.087915+00:00
-- url     : https://prove2.me/submissions/08eb00a9-cf48-4149-a0a7-20acd3375802

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
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
theorem _root_.solution [CharZero k] (A : Module.End k W)
    (B : Module.End k W')
    (h : ∀ m, 0 < m → LinearMap.trace k W (A ^ m) = LinearMap.trace k W' (B ^ m)) :
    A.charpoly.reverse = B.charpoly.reverse := by
  set P : PowerSeries k := ((A.charpoly.reverse : k[X]) : PowerSeries k) with hPdef
  set Q : PowerSeries k := ((B.charpoly.reverse : k[X]) : PowerSeries k) with hQdef
  set D : PowerSeries k := PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1))
  have hP : PowerSeries.constantCoeff P = 1 := constantCoeff_reverse_charpoly A
  have hQ : PowerSeries.constantCoeff Q = 1 := constantCoeff_reverse_charpoly B
  have hQQ : Q⁻¹ * Q = 1 := PowerSeries.inv_mul_cancel Q (by rw [hQ]; exact one_ne_zero)
  have hdP : PowerSeries.derivative k P = -P * D := by
    rw [hPdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
  have hdQ : PowerSeries.derivative k Q = -Q * D := by
    rw [hQdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
    congr 2
    funext m
    exact (h (m + 1) m.succ_pos).symm
  have h1 : P * Q⁻¹ = 1 := by
    apply PowerSeries.derivative.ext
    · rw [Derivation.leibniz, PowerSeries.derivative_inv', hdP, hdQ,
        Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul]
      linear_combination (P * Q⁻¹ * D) * hQQ
    · rw [map_mul, PowerSeries.constantCoeff_inv, hP, hQ, map_one, inv_one, mul_one]
  have h2 : P = Q := by
    calc P = P * (Q⁻¹ * Q) := by rw [hQQ, mul_one]
      _ = Q := by rw [← mul_assoc, h1, one_mul]
  exact Polynomial.coe_inj.1 h2
end GroundTheory.Global
