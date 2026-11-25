-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.laurent_ode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:55:33.288771+00:00
-- url     : https://prove2.me/submissions/90841265-46f5-4992-9013-da41579b0239

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_eq_except_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_deriv_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_eq_except_zero

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
theorem _root_.solution :
    (fun z ↦ z ^ 2 * (deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) + L.g₂ / 2)) =ᶠ[𝓝 0]
      (fun z ↦ 12 * ℘[L - (0 : ℂ)] z) := by
  have hVo : IsOpen (↑L.lattice \ {(0 : ℂ)})ᶜ := L.isOpen_compl_lattice_sdiff
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp
  have hzL : z ∉ L.lattice := fun h ↦ hz ⟨h, hz0⟩
  have h1 : deriv ℘[L - (0 : ℂ)] =ᶠ[𝓝 z] ℘'[L - (0 : ℂ)] := by
    filter_upwards [hVo.mem_nhds hz] with u hu
    exact L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hu
  rw [h1.deriv_eq]
  have hP'a : DifferentiableAt ℂ ℘'[L - (0 : ℂ)] z :=
    (L.analyticOnNhd_derivWeierstrassPExcept 0 z hz).differentiableAt
  have hq : HasDerivAt (fun u ↦ ℘'[L - (0 : ℂ)] u - 2 / u ^ 3)
      (deriv ℘'[L - (0 : ℂ)] z + 6 / z ^ 4) z :=
    (hP'a.hasDerivAt.sub ((hasDerivAt_const z (2 : ℂ)).div (hasDerivAt_pow 3 z)
      (pow_ne_zero 3 hz0))).congr_deriv (by field_simp; ring)
  have heq : ℘'[L] = fun u ↦ ℘'[L - (0 : ℂ)] u - 2 / u ^ 3 :=
    funext derivWeierstrassP_eq_except_zero
  have hval := deriv_derivWeierstrassP hzL
  rw [heq, hq.deriv, weierstrassP_eq_except_zero z] at hval
  have hd : deriv ℘'[L - (0 : ℂ)] z =
      6 * (℘[L - (0 : ℂ)] z + 1 / z ^ 2) ^ 2 - L.g₂ / 2 - 6 / z ^ 4 := by
    linear_combination hval
  rw [hd]
  field_simp
  ring
end GroundTheory.Global.Elliptic
