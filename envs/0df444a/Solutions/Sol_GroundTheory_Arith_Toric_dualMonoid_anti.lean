-- Prove2me | solution 1 for GroundTheory.Arith.Toric.dualMonoid_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:50.513055+00:00
-- url     : https://prove2.me/submissions/fa3a2414-8a86-4697-9fb2-870c279acd68

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Theorems.Thm_GroundTheory_Arith_Toric_mem_dualMonoid


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
theorem _root_.solution {σ₁ σ₂ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : σ₁ ≤ σ₂) :
    dualMonoid σ₂ ≤ dualMonoid σ₁ :=
  fun _ hm => mem_dualMonoid.2 fun x hx => mem_dualMonoid.1 hm x (h hx)
end GroundTheory.Arith.Toric
