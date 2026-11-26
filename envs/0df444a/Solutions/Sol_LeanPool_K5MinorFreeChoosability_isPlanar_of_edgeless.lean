-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.isPlanar_of_edgeless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:31.625444+00:00
-- url     : https://prove2.me/submissions/06f4d223-da1b-4ee0-a9fe-bcc8454270ec

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite V] (h : ∀ u v, ¬ G.Adj u v) : IsPlanar G := by
  have hD : IsEmpty G.Dart := ⟨fun d => h _ _ d.adj⟩
  refine ⟨⟨1, ⟨fun d => hD.elim d, fun d => hD.elim d⟩, ?_⟩⟩
  unfold eulerDefect numComponents cycleCount numClasses
  simp [Nat.card_of_isEmpty]
end LeanPool.K5MinorFreeChoosability
