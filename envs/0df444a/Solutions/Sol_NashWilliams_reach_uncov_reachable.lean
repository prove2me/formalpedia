-- Prove2me | solution 1 for NashWilliams.reach_uncov_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:04:29.288644+00:00
-- url     : https://prove2.me/submissions/d2979369-a1e2-46d4-bf00-f60f00dcfb14

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_not_reachable_deleteEdges_of_mem_edges
public import Theorems.Thm_NashWilliams_reachable_of_uncov
public import Theorems.Thm_NashWilliams_Step_uncov
public import Theorems.Thm_NashWilliams_exchGraph_adj
public import Theorems.Thm_NashWilliams_reach_valid

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable {G : SimpleGraph V} {k : ℕ}
variable [Finite V] {F₀ : Fin k → SimpleGraph V} (hF₀ : Valid G F₀)
  (hmax : ∀ F : Fin k → SimpleGraph V, Valid G F → total F ≤ total F₀)
include hF₀ hmax
namespace NashWilliams
theorem _root_.solution {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) {u v : V} (huv : Uncov G F u v) (i : Fin k) :
    (F i ⊓ exchGraph G F₀).Reachable u v := by
  classical
  obtain ⟨hval, htot⟩ := reach_valid hF₀ hF
  have hr := reachable_of_uncov hval (fun F' hF' ↦ htot ▸ hmax F' hF') huv i
  obtain ⟨w⟩ := hr
  set p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  refine ⟨p.transfer _ fun e he ↦ ?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : (F i).Adj x y := p.edges_subset_edgeSet he
    refine ⟨hxy, exchGraph_adj.2
      ⟨update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v), ?_, Step.uncov hval huv hxy⟩⟩
    refine hF.tail ⟨i, u, v, x, y, huv, hxy, ?_, rfl⟩
    exact ((hval.1 i).2.anti (deleteEdges_le _)).sup_edge_of_not_reachable
      (not_reachable_deleteEdges_of_mem_edges (hval.1 i).2 p hp he)
end NashWilliams
