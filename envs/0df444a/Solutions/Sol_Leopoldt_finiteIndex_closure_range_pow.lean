-- Prove2me | solution 1 for Leopoldt.finiteIndex_closure_range_pow
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:01:06.238723+00:00
-- url     : https://prove2.me/submissions/d2f873ee-79fc-4cdc-a55e-d026724a3df0

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness

theorem solution (G : Type*) [CommGroup G]
    (ι : Type*) [Finite ι] (f : ι → G)
    (h : (Subgroup.closure (Set.range f)).FiniteIndex)
    (n : ℕ) (hn : n ≠ 0) :
    (Subgroup.closure (Set.range fun i => f i ^ n)).FiniteIndex := by
  let B : Subgroup G := Subgroup.closure (Set.range f)
  have hB : B.FiniteIndex := h
  have hfg : B.FG := by
    apply (Subgroup.fg_iff B).2
    exact ⟨Set.range f, rfl, Set.finite_range f⟩
  have hrel : (B.map (powMonoidHom (α := G) n)).IsFiniteRelIndex B :=
    Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg hfg hn
  have hle : B.map (powMonoidHom (α := G) n) ≤ B := by
    rintro x ⟨y, hy, rfl⟩
    exact B.pow_mem hy n
  have hpow : (B.map (powMonoidHom (α := G) n)).FiniteIndex := by
    apply Subgroup.finiteIndex_iff.mpr
    rw [← Subgroup.relIndex_mul_index hle]
    exact mul_ne_zero hrel.relIndex_ne_zero hB.index_ne_zero
  letI : (B.map (powMonoidHom (α := G) n)).FiniteIndex := hpow
  apply Subgroup.finiteIndex_of_le (H := B.map (powMonoidHom (α := G) n))
  change (Subgroup.closure (Set.range f)).map (powMonoidHom (α := G) n) ≤ _
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, rfl⟩
