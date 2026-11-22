-- Prove2me | solution 1 for NormedVectorLattice.norm_le_norm_abs_sup_abs_of_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:22.533908+00:00
-- url     : https://prove2.me/submissions/24de5c5f-d298-4010-ab85-991b4143638c

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
theorem _root_.solution {a b x : X} (hx : x ∈ Set.Icc a b) :
    ‖x‖ ≤ ‖|a| ⊔ |b|‖ := by
  rw [← norm_abs_eq_norm x]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (le_sup_of_le_left (abs_nonneg a))]
  rw [abs]
  apply sup_le
  · rw [abs]
    apply sup_le
    · exact le_trans hx.2 (le_trans (le_abs_self b) le_sup_right)
    · exact le_trans (neg_le_neg hx.1) (le_trans (neg_le_abs a) le_sup_left)
  · exact le_trans (neg_nonpos_of_nonneg (abs_nonneg x))
      (le_sup_of_le_left (abs_nonneg a))
end NormedVectorLattice
