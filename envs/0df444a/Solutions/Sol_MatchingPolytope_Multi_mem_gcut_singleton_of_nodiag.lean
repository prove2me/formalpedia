-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_gcut_singleton_of_nodiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:18.52365+00:00
-- url     : https://prove2.me/submissions/187e92ab-d83a-4223-86ea-da681b239b10

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_exists_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {D : Finset E} (hD : ∀ e ∈ D, ¬ (ends e).IsDiag) {e : E}
    {v : V} : e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e := by
  classical
  constructor
  · intro h
    obtain ⟨hD', ⟨u, hu, hu'⟩, -⟩ := Finset.mem_filter.1 h
    rw [Finset.mem_singleton] at hu'
    exact ⟨hD', hu' ▸ hu⟩
  · rintro ⟨he, hv⟩
    obtain ⟨a, b, h⟩ := exists_pair (ends e)
    have hab : a ≠ b := fun hab => hD e he (by simp [h, hab])
    rw [mem_gcut_of_pair h]
    rw [h, Sym2.mem_iff] at hv
    refine ⟨he, ?_⟩
    rcases hv with rfl | rfl
    · simp [Ne.symm hab]
    · simp [hab]
end MatchingPolytope.Multi
