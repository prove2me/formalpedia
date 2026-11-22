-- Prove2me | solution 1 for NormedVectorLattice.lipschitzWith_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:50.114208+00:00
-- url     : https://prove2.me/submissions/bf2f7e78-c3f6-450d-a9af-84f91a721a8a

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed

set_option autoImplicit true
@[expose] public section
public section
open NormedVectorLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
namespace NormedVectorLattice
theorem _root_.solution : LipschitzWith 1 (|·| : X → X) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_abs_sub_abs a b
end NormedVectorLattice
