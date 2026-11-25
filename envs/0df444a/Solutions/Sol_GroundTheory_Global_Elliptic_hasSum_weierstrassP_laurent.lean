-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.hasSum_weierstrassP_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:12.002333+00:00
-- url     : https://prove2.me/submissions/72bbca0f-6426-44a7-aa85-8106eeaf3683

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
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
theorem _root_.solution {z : ℂ} (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖) :
    HasSum (fun j ↦ weierstrassLaurentCoeff L j * z ^ j) (℘[L] z - 1 / z ^ 2) := by
  have h := L.weierstrassPExceptSeries_hasSum 0 z 0 (fun l hl ↦ by simpa using hz l hl)
  rw [weierstrassP_eq_except_zero z, add_sub_cancel_right]
  convert h using 2 with j
  rw [sub_zero, PeriodPair.weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
    weierstrassLaurentCoeff]
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · simp [hj, L.lattice.zero_mem, L.sumInvPow_zero]
end GroundTheory.Global.Elliptic
