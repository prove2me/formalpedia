-- Prove2me | solution 1 for IsVLDisjoint.mono_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:42.274602+00:00
-- url     : https://prove2.me/submissions/fe875d3b-d8e0-450d-9071-6c490e91b3e3

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
namespace IsVLDisjoint
theorem _root_.solution {x y z : X} (h : IsVLDisjoint x y)
    (hzy : |z| ≤ |y|) : IsVLDisjoint x z := by
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |z| ≤ |x| ⊓ |y| := inf_le_inf_left _ hzy
    _ = 0 := h
end IsVLDisjoint
