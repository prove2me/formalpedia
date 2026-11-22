-- Prove2me | solution 1 for LatinQuarter.defining_iff_completions_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:24.530486+00:00
-- url     : https://prove2.me/submissions/3d4354fe-3ad5-446f-81bb-23b49ac39b8e

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ}
    (P : Finset (Cell n)) (L : Square n) :
    IsDefining P L ↔ completions P L = {L} := by
  classical
  constructor
  · rintro ⟨hL, hu⟩
    ext M
    simp only [mem_completions, Finset.mem_singleton]
    constructor
    · rintro ⟨hM, ha⟩
      exact hu M hM ha
    · rintro rfl
      exact ⟨hL, fun _ _ => rfl⟩
  · intro h
    have hL : L ∈ completions P L := by simp [h]
    refine ⟨(mem_completions.mp hL).1, ?_⟩
    intro M hM ha
    have hm : M ∈ completions P L := mem_completions.mpr ⟨hM, ha⟩
    simpa [h] using hm
end LatinQuarter
