-- Prove2me | solution 1 for GroundTheory.Arith.Toric.toRealDual_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:23.962386+00:00
-- url     : https://prove2.me/submissions/8073a2ee-c350-432e-b559-26738260fdde

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution : Function.Injective (toRealDual N) := by
  intro m m' h
  refine LinearMap.ext fun n => ?_
  have := congrArg (fun f => f (toRealSpan N n)) h
  simp only [toRealDual_apply_toRealSpan] at this
  exact_mod_cast this
end GroundTheory.Arith.Toric
