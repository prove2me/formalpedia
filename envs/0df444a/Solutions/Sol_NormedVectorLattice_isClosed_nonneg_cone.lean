-- Prove2me | solution 1 for NormedVectorLattice.isClosed_nonneg_cone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:55.798805+00:00
-- url     : https://prove2.me/submissions/fc549280-ce2c-4ee2-9135-ff52736d2422

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
theorem _root_.solution : IsClosed {x : X | 0 ≤ x} := isClosed_nonneg
end NormedVectorLattice
