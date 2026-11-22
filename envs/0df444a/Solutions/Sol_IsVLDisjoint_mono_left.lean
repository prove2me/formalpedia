-- Prove2me | solution 1 for IsVLDisjoint.mono_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:19.925516+00:00
-- url     : https://prove2.me/submissions/5bf68b03-8b24-4e4e-bae1-0864539b6b79

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_IsVLDisjoint_mono_right

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
namespace IsVLDisjoint
theorem _root_.solution {x y z : X} (h : IsVLDisjoint x y)
    (hzx : |z| ≤ |x|) : IsVLDisjoint z y :=
  isVLDisjoint_comm.mp ((isVLDisjoint_comm.mp h).mono_right hzx)
end IsVLDisjoint
