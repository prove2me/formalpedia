-- Prove2me | solution 1 for IsVLDisjoint.sup_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:30.365802+00:00
-- url     : https://prove2.me/submissions/2148cc91-4a45-48fb-a6b2-0c2ddd7d9693

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_IsVLDisjoint_sup_right

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
namespace IsVLDisjoint
theorem _root_.solution {x y z : X}
    (hx : IsVLDisjoint x z) (hy : IsVLDisjoint y z) :
    IsVLDisjoint (x ⊔ y) z :=
  isVLDisjoint_comm.mp
    (IsVLDisjoint.sup_right (isVLDisjoint_comm.mp hx) (isVLDisjoint_comm.mp hy))
end IsVLDisjoint
