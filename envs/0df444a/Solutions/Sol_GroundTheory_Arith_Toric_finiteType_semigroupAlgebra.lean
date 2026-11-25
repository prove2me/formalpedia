-- Prove2me | solution 1 for GroundTheory.Arith.Toric.finiteType_semigroupAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:18.977633+00:00
-- url     : https://prove2.me/submissions/b660ed58-4f97-4deb-821c-67f44ae80327

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Theorems.Thm_GroundTheory_Arith_Toric_semigroupAlgebra_closure

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
theorem _root_.solution {S : AddSubmonoid G} (hS : S.FG) :
    Algebra.FiniteType k (semigroupAlgebra k S) := by
  classical
  obtain ⟨T, rfl⟩ := hS
  rw [← Subalgebra.fg_iff_finiteType, semigroupAlgebra_closure]
  exact ⟨T.image fun s => single s (1 : k), by rw [Finset.coe_image]⟩
end GroundTheory.Arith.Toric
