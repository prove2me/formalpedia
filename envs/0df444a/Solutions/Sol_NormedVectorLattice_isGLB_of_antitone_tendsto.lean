-- Prove2me | solution 1 for NormedVectorLattice.isGLB_of_antitone_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:07.006859+00:00
-- url     : https://prove2.me/submissions/6f0dc143-3efa-40b1-b7c8-48d3fb62f5be

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
theorem _root_.solution {u : ℕ → X} {l : X}
    (hanti : Antitone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsGLB (Set.range u) l :=
  isGLB_of_tendsto_atTop hanti hlim
end NormedVectorLattice
