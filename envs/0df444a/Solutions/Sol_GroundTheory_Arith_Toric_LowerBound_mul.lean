-- Prove2me | solution 1 for GroundTheory.Arith.Toric.LowerBound.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:40:34.411592+00:00
-- url     : https://prove2.me/submissions/5e308508-eded-444d-9bbd-bec315e0626b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
variable {φ}
namespace GroundTheory.Arith.Toric
namespace LowerBound
theorem _root_.solution {f g : AddMonoidAlgebra k G} {a b : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g b) : LowerBound φ (f * g) (a + b) := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  rw [map_add]
  exact add_le_add (hf x hx) (hg y hy)
end LowerBound
end GroundTheory.Arith.Toric
