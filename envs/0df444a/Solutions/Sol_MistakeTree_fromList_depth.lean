-- Prove2me | solution 1 for MistakeTree.fromList_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:40.030419+00:00
-- url     : https://prove2.me/submissions/79d7a000-243e-4d72-92ea-6030cf633eff

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone

set_option autoImplicit true
@[expose] public section
public section
universe u v
namespace MistakeTree
theorem _root_.solution {X : Type u} :
    ∀ (l : List X), (MistakeTree.fromList l).depth = l.length
  | [] => rfl
  | _ :: xs => by
    simp only [MistakeTree.fromList, MistakeTree.depth, solution xs, Nat.max_self,
      List.length_cons]
    omega
end MistakeTree
