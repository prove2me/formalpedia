-- Prove2me | solution 1 for GroundTheory.Arith.Toric.semigroupAlgebra_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:33.948051+00:00
-- url     : https://prove2.me/submissions/3b89f6a0-c404-4da8-9679-7d004e6dbbdf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]
variable {k}
namespace GroundTheory.Arith.Toric
theorem _root_.solution (T : Set G) :
    semigroupAlgebra k (AddSubmonoid.closure T) =
      Algebra.adjoin k ((fun s => single s (1 : k)) '' T) := by
  apply le_antisymm
  · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    induction hs using AddSubmonoid.closure_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero =>
      show single (0 : G) (1 : k) ∈ _
      rw [← AddMonoidAlgebra.one_def]; exact Subalgebra.one_mem _
    | add x y _ _ hx hy =>
      have e : single (x + y) (1 : k) = single x 1 * single y 1 := by
        rw [single_mul_single, one_mul]
      show single (x + y) (1 : k) ∈ _
      rw [e]
      exact Subalgebra.mul_mem _ hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact single_mem_semigroupAlgebra (AddSubmonoid.subset_closure hs) 1
end GroundTheory.Arith.Toric
