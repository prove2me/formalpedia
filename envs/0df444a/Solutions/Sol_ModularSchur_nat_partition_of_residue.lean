-- Prove2me | solution 1 for ModularSchur.nat_partition_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:42:11.240465+00:00
-- url     : https://prove2.me/submissions/e1022d41-19d5-4b11-b1e6-75bffe11c495

-- Generated from lean/ModularSchur/IntegerBridge.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : nat_partition_of_residue -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open Finset
variable {m : ℕ}

open ModularSchur in
theorem solution (_hm : 2 ≤ m) {ℓ k N : ℕ} (_hN : N ≤ m - 1)
    {Q : Fin k → Finset (ZMod m)} (hQ : IsValidPartition m ℓ k (stableResidues m N) Q) :
    ∃ P : Fin k → Finset ℕ, IsValidPartitionNat m ℓ k N P := by
  refine ⟨fun i => (Finset.Ioc 0 N).filter (fun a => (a : ZMod m) ∈ Q i), ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha_img : (a : ZMod m) ∈ stableResidues m N :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := hQ.covers _ ha_img
    exact ⟨i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  · intro i j hij
    rw [Finset.disjoint_filter]
    intro a _ hai haj
    exact (Finset.disjoint_iff_ne.mp (hQ.disjoint i j hij)) _ hai _ haj rfl
  · intro i a ha
    exact (Finset.mem_filter.mp ha).1
  · intro i f hf y hy hsum
    have hf_cast : ∀ j, (f j : ZMod m) ∈ Q i := fun j =>
      (Finset.mem_filter.mp (hf j)).2
    have hy_cast : (y : ZMod m) ∈ Q i := (Finset.mem_filter.mp hy).2
    have hsum_cast : (((∑ j, f j) : ℕ) : ZMod m) = (y : ZMod m) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact hsum
    have hsum' : (∑ j, ((f j : ℕ) : ZMod m)) = (y : ZMod m) := by
      push_cast at hsum_cast; exact hsum_cast
    exact hQ.sumFree i (fun j => (f j : ZMod m)) hf_cast (y : ZMod m) hy_cast hsum'
