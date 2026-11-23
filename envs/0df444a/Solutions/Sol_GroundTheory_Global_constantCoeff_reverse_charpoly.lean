-- Prove2me | solution 1 for GroundTheory.Global.constantCoeff_reverse_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:08.690995+00:00
-- url     : https://prove2.me/submissions/b82f872e-eaa2-4255-9bfa-a937e663c0b3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly

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
    PowerSeries.constantCoeff (A.charpoly.reverse : PowerSeries k) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
    (LinearMap.charpoly_monic A).leadingCoeff]
end GroundTheory.Global
