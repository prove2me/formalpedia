-- Prove2me | solution 1 for NormedVectorLattice.isClosed_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:12.281036+00:00
-- url     : https://prove2.me/submissions/53f2115e-cf1d-4ff6-8bc4-24228e494cfb

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
theorem _root_.solution (a b : X) : IsClosed (Set.Icc a b) := isClosed_Icc
end NormedVectorLattice
