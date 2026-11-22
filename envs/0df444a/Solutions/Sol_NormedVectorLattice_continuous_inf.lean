-- Prove2me | solution 1 for NormedVectorLattice.continuous_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:49.480952+00:00
-- url     : https://prove2.me/submissions/b6af4a77-a4b3-4cbe-b989-7f4e388573fa

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
theorem _root_.solution : Continuous (fun p : X × X => p.1 ⊓ p.2) :=
  ContinuousInf.continuous_inf
end NormedVectorLattice
