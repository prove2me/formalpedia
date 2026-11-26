-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:47.622175+00:00
-- url     : https://prove2.me/submissions/79b0fbb3-09d0-4191-9698-672470746701

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (σ α : Perm (Subtype p)) (u v : D) (hu : ¬ p u)
    (h : compSetoid (ofSubtype σ) (ofSubtype α) u v) : u = v := by
  have := compSetoid_le (Setoid.ker fun w => if p w then none else some w)
    (fun z => by
      rw [Setoid.ker_def]
      by_cases hz : p z
      · have h1 := ofSubtype_apply_of_mem σ hz
        have h2 : p (ofSubtype σ z) := h1 ▸ (σ ⟨z, hz⟩).2
        simp [hz, h2]
      · rw [ofSubtype_apply_of_not_mem σ hz])
    (fun z => by
      rw [Setoid.ker_def]
      by_cases hz : p z
      · have h1 := ofSubtype_apply_of_mem α hz
        have h2 : p (ofSubtype α z) := h1 ▸ (α ⟨z, hz⟩).2
        simp [hz, h2]
      · rw [ofSubtype_apply_of_not_mem α hz]) h
  rw [Setoid.ker_def] at this
  by_cases hv : p v
  · simp [hu, hv] at this
  · simpa [hu, hv] using this
end LeanPool.K5MinorFreeChoosability
