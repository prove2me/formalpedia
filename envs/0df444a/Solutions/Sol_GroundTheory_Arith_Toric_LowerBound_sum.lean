-- Prove2me | solution 1 for GroundTheory.Arith.Toric.LowerBound.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:26.101665+00:00
-- url     : https://prove2.me/submissions/75b7f053-25e0-4b15-a93a-ed8fb95fecc9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Theorems.Thm_GroundTheory_Arith_Toric_lowerBound_zero

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → AddMonoidAlgebra k G} {a : ℤ}
    (hf : ∀ i ∈ s, LowerBound φ (f i) a) : LowerBound φ (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerBound_zero a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end LowerBound
end GroundTheory.Arith.Toric
