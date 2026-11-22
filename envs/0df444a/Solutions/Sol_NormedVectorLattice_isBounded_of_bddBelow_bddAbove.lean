-- Prove2me | solution 1 for NormedVectorLattice.isBounded_of_bddBelow_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:12.815113+00:00
-- url     : https://prove2.me/submissions/e1e08424-fb0b-42e0-a40a-3a1f2bc86dad

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Theorems.Thm_NormedVectorLattice_norm_le_norm_abs_sup_abs_of_mem_Icc

set_option autoImplicit true
@[expose] public section
public section
open NormedVectorLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
namespace NormedVectorLattice
theorem _root_.solution {s : Set X}
    (hl : BddBelow s) (hu : BddAbove s) : Bornology.IsBounded s := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  rw [Metric.isBounded_iff_subset_closedBall (0 : X)]
  exact ⟨‖|a| ⊔ |b|‖, fun x hx => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_norm_abs_sup_abs_of_mem_Icc ⟨ha hx, hb hx⟩⟩
end NormedVectorLattice
