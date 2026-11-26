-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_dartSymm_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:20:20.75616+00:00
-- url     : https://prove2.me/submissions/6f3e1a19-2fc5-4dae-a0b6-6b87f37321e3

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step

attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {d e : G.Dart} :
    SameCycle (dartSymm G) d e ↔ e = d ∨ e = d.symm := by
  constructor
  · intro h
    have := sameCycle_of_step (Setoid.ker SimpleGraph.Dart.edge) (fun z => by
      rw [Setoid.ker_def]; simp) h
    rw [Setoid.ker_def, SimpleGraph.dart_edge_eq_iff] at this
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact SameCycle.refl _ _
    · exact ⟨1, by simp⟩
end LeanPool.K5MinorFreeChoosability
