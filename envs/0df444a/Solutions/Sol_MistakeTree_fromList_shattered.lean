-- Prove2me | solution 1 for MistakeTree.fromList_shattered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:28.716884+00:00
-- url     : https://prove2.me/submissions/0c87d0c7-7456-43bb-89c1-a999755703ce

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Theorems.Thm_Shatters_subset

set_option autoImplicit true
@[expose] public section
public section
universe u v
namespace MistakeTree
theorem _root_.solution {X : Type u} [DecidableEq X] {C : ConceptClass X Bool}
    (l : List X) (hl : l.Nodup) (hS : Shatters X C l.toFinset) :
    (MistakeTree.fromList l).isShattered X C := by
  induction l with
  | nil => exact trivial
  | cons x xs ih =>
    unfold fromList isShattered
    have hnd := (List.nodup_cons.mp hl).2
    have hxS : x ∈ (x :: xs).toFinset := by simp
    have hsub : xs.toFinset ⊆ (x :: xs).toFinset := by
      simp_all
    have hxs_shat : Shatters X C xs.toFinset := hS.subset hsub
    refine ⟨?_, ?_⟩
    · obtain ⟨c, hcC, hc⟩ := hS (fun _ => true)
      exact ⟨c, hcC, hc ⟨x, hxS⟩, ih hnd hxs_shat⟩
    · obtain ⟨c, hcC, hc⟩ := hS (fun _ => false)
      exact ⟨c, hcC, hc ⟨x, hxS⟩, ih hnd hxs_shat⟩
end MistakeTree
