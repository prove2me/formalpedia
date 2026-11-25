-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.iteratedDeriv_weierstrassPExcept_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:48.331239+00:00
-- url     : https://prove2.me/submissions/8beeceb6-2c8b-4c2d-8894-881d48bdc544

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
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
theorem _root_.solution (j : ℕ) :
    iteratedDeriv j ℘[L - (0 : ℂ)] 0 = j ! * weierstrassLaurentCoeff L j := by
  rw [L.iteratedDeriv_weierstrassPExcept_self 0, weierstrassLaurentCoeff]
  split_ifs with h
  · simp
  · rw [L.sumInvPow_zero, Nat.factorial_succ]
    push_cast
    ring
end GroundTheory.Global.Elliptic
