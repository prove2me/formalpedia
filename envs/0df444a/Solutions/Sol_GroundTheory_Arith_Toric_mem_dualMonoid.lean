-- Prove2me | solution 1 for GroundTheory.Arith.Toric.mem_dualMonoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:35.171497+00:00
-- url     : https://prove2.me/submissions/a1cb6928-86bf-4f20-ab3a-6b2add93bdbf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice

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
theorem _root_.solution {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)} {m : Dual ℤ N} :
    m ∈ dualMonoid σ ↔ ∀ x ∈ σ, 0 ≤ toRealDual N m x := Iff.rfl
end GroundTheory.Arith.Toric
