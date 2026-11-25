-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.laurent_ode_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:25.90155+00:00
-- url     : https://prove2.me/submissions/d796d382-6872-46d5-bd91-2ea5e8a73a72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_laurent_ode
import Theorems.Thm_GroundTheory_Global_Elliptic_choose_two_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two

set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (k : ℕ) :
    ((k + 2 : ℂ) * (k + 1)) * (iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 -
      6 * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * iteratedDeriv j ℘[L - (0 : ℂ)] 0 *
        iteratedDeriv (k - j) ℘[L - (0 : ℂ)] 0 + (if k = 0 then L.g₂ / 2 else 0)) =
      12 * iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  have hPP : AnalyticAt ℂ (fun z ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 := hP.mul hP
  have hQ : AnalyticAt ℂ (deriv (deriv ℘[L - (0 : ℂ)])) 0 := hP.deriv.deriv
  have h6 : AnalyticAt ℂ (fun z ↦ 6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z)) 0 :=
    analyticAt_const.mul hPP
  have hA : AnalyticAt ℂ (fun z ↦ deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z)) 0 := hQ.sub h6
  have hW : AnalyticAt ℂ (fun z ↦ deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) + L.g₂ / 2) 0 := hA.add analyticAt_const
  have hsq : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) 0 := by fun_prop
  have e := (laurent_ode (L := L)).iteratedDeriv_eq (k + 2)
  rw [iteratedDeriv_fun_mul hsq.contDiffAt hW.contDiffAt,
    iteratedDeriv_const_mul_field] at e
  rw [Finset.sum_eq_single 2 (fun i _ hi ↦ by rw [iteratedDeriv_fun_pow_zero, if_neg hi]; simp)
    (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h)] at e
  rw [iteratedDeriv_fun_add hA.contDiffAt analyticAt_const.contDiffAt,
    iteratedDeriv_fun_sub hQ.contDiffAt h6.contDiffAt, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hP.contDiffAt hP.contDiffAt, iteratedDeriv_const,
    ← iteratedDeriv_succ', ← iteratedDeriv_succ', iteratedDeriv_fun_pow_zero,
    show k + 2 - 2 = k by omega] at e
  simp only [if_true, Nat.factorial_two, Nat.cast_ofNat] at e
  rw [← e, ← choose_two_mul k]
end GroundTheory.Global.Elliptic
