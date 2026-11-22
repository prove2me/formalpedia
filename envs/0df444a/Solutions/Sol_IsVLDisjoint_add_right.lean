-- Prove2me | solution 1 for IsVLDisjoint.add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:47.76607+00:00
-- url     : https://prove2.me/submissions/9c5813b9-42af-4fe3-a3f4-5684dbb8fe2d

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
namespace IsVLDisjoint
theorem _root_.solution {x y z : X}
    (hy : IsVLDisjoint x y) (hz : IsVLDisjoint x z) :
    IsVLDisjoint x (y + z) := by
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |y + z| ≤ |x| ⊓ (|y| + |z|) := inf_le_inf_left _ (abs_add_le y z)
    _ ≤ |x| ⊓ |y| + |x| ⊓ |z| := inf_le_inf_add_inf_of_nonneg _ _ _
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    _ = 0 := by rw [hy, hz, add_zero]
end IsVLDisjoint
