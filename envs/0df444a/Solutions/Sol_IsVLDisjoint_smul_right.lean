-- Prove2me | solution 1 for IsVLDisjoint.smul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:28.143818+00:00
-- url     : https://prove2.me/submissions/b7274461-734b-41e2-af92-6eda7efa76a9

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_IsVLDisjoint_smul_left

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace IsVLDisjoint
theorem _root_.solution {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint x (a • y) :=
  isVLDisjoint_comm.mp ((isVLDisjoint_comm.mp h).smul_left a)
end IsVLDisjoint
