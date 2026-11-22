-- Prove2me | solution 1 for IsVLDisjoint.sup_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:48.004971+00:00
-- url     : https://prove2.me/submissions/b6219cc2-3864-43fc-80e9-d53a3f1bce9c

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
    IsVLDisjoint x (y ⊔ z) := by
  have habs : |y ⊔ z| ≤ |y| + |z| := by
    rw [abs]
    refine sup_le ?_ ?_
    · exact sup_le ((le_abs_self y).trans
        (le_add_of_nonneg_right (abs_nonneg _)))
        ((le_abs_self z).trans (le_add_of_nonneg_left (abs_nonneg _)))
    · rw [neg_sup]
      exact inf_le_left.trans ((neg_le_abs y).trans
        (le_add_of_nonneg_right (abs_nonneg _)))
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |y ⊔ z| ≤ |x| ⊓ (|y| + |z|) := inf_le_inf_left _ habs
    _ ≤ |x| ⊓ |y| + |x| ⊓ |z| := inf_le_inf_add_inf_of_nonneg _ _ _
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    _ = 0 := by rw [hy, hz, add_zero]
end IsVLDisjoint
