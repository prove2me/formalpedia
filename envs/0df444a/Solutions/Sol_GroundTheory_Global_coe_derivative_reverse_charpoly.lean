-- Prove2me | solution 1 for GroundTheory.Global.coe_derivative_reverse_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:42.591348+00:00
-- url     : https://prove2.me/submissions/aa841e09-5f08-40dc-8c0e-7afa4e76fcf5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Theorems.Thm_GroundTheory_Global_coe_derivative_charpolyRev
import Theorems.Thm_GroundTheory_Global_reverse_charpoly_eq_charpolyRev

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
theorem _root_.solution (A : Module.End k W) :
    ((derivative A.charpoly.reverse : k[X]) : PowerSeries k) =
      -(A.charpoly.reverse : PowerSeries k) *
        PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1)) := by
  classical
  let b := Module.Free.chooseBasis k W
  rw [reverse_charpoly_eq_charpolyRev b, coe_derivative_charpolyRev]
  congr 2
  funext m
  rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_pow]
end GroundTheory.Global
