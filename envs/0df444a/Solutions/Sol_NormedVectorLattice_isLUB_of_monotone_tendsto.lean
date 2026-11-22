-- Prove2me | solution 1 for NormedVectorLattice.isLUB_of_monotone_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:06.50938+00:00
-- url     : https://prove2.me/submissions/085185d1-68b3-474c-a0f5-c07bbc7edbaa

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
    (hmono : Monotone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsLUB (Set.range u) l :=
  isLUB_of_tendsto_atTop hmono hlim
end NormedVectorLattice
