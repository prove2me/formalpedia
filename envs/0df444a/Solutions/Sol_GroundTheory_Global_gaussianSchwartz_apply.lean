-- Prove2me | solution 1 for GroundTheory.Global.gaussianSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:51.152719+00:00
-- url     : https://prove2.me/submissions/05765990-5349-436b-8819-2c26effbd946

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Real Function
open scoped ContDiff Nat SchwartzMap
open GroundTheory GroundTheory.Global
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GroundTheory.Global
theorem _root_.solution (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
  rfl
end GroundTheory.Global
