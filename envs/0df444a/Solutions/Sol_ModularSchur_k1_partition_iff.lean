-- Prove2me | solution 1 for ModularSchur.k1_partition_iff
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:40:40.303187+00:00
-- url     : https://prove2.me/submissions/f550d29e-b919-4596-8ef3-88e37221f014

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : k1_partition_iff -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open Finset Classical

open ModularSchur in
theorem solution (m ℓ : ℕ) (T : Finset (ZMod m)) :
    (∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 T P) ↔
    IsEllSumFree m ℓ T := by
  constructor
  · rintro ⟨P, hP⟩
    have hcov : T ⊆ P 0 := by
      intro x hx
      obtain ⟨i, hi⟩ := hP.covers x hx
      have : i = 0 := Subsingleton.elim i 0
      rwa [this] at hi
    have heq : P 0 = T := Finset.Subset.antisymm (hP.subset 0) hcov
    exact heq ▸ hP.sumFree 0
  · intro hT
    exact ⟨fun _ => T, {
      covers   := fun x hx => ⟨0, hx⟩
      disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
      subset   := fun _ => le_refl T
      sumFree  := fun _ => hT }⟩
