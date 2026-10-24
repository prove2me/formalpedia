-- Prove2me | solution 1 for NashWilliams61.TreePacking.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:14:58.881172+00:00
-- url     : https://prove2.me/submissions/cf885af9-1188-4385-9017-e3ad14339083

import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Lean.Elab.Tactic.Omega

open NagamochiIbaraki.EdgeConn

namespace D24SpanningTree

lemma lift_reachable {V : Type*} {G H : SimpleGraph V}
    (h : ∀ {x y}, G.Adj x y → H.Reachable x y) {x y : V}
    (hr : G.Reachable x y) : H.Reachable x y := by
  rcases hr with ⟨p⟩
  induction p with
  | nil => exact .rfl
  | cons ha p ih => exact (h ha).trans ih

lemma erase_preserves {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) (T : Finset E) (e : E) (u v : V)
    (he : ends e = s(u, v)) (hr : (edgeGraph ends (T.erase e)).Reachable u v) :
    ∀ {x y}, (edgeGraph ends T).Reachable x y →
      (edgeGraph ends (T.erase e)).Reachable x y := by
  classical
  apply lift_reachable
  intro x y hadj
  rcases (SimpleGraph.fromEdgeSet_adj _).mp hadj with ⟨⟨f, hf, hfe⟩, hxy⟩
  by_cases h : f = e
  · subst f
    have hp : s(x, y) = s(u, v) := hfe.symm.trans he
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact hr.symm
  · apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    exact ⟨⟨f, Finset.mem_erase.mpr ⟨h, hf⟩, hfe⟩, hxy⟩

end D24SpanningTree

open NashWilliams61.TreePacking

theorem solution {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (W : Finset V) (F : Finset E)
    (hF : ∀ e ∈ F, ∀ v ∈ ends e, v ∈ W) (hW : W.Nonempty)
    (hconn : ∀ u ∈ W, ∀ v ∈ W, (edgeGraph ends F).Reachable u v) :
    ∃ T : Finset E, IsSpanningTreeOn ends W F T := by
  classical
  let C := F.powerset.filter fun T =>
    ∀ u ∈ W, ∀ v ∈ W, (edgeGraph ends T).Reachable u v
  have hFC : F ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl), hconn⟩
  obtain ⟨T, hTC, hmin⟩ := Finset.exists_min_image C Finset.card ⟨F, hFC⟩
  have hsub : T ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hTC).1
  have hconT := (Finset.mem_filter.mp hTC).2
  refine ⟨T, hsub, hW, ?_, ?_, hconT⟩
  · intro e he v hv
    exact hF e (hsub he) v hv
  · intro e he u v huv hr
    have hc : T.erase e ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ((Finset.erase_subset e T).trans hsub), ?_⟩
      intro x hx y hy
      exact D24SpanningTree.erase_preserves ends T e u v huv hr (hconT x hx y hy)
    have hle := hmin (T.erase e) hc
    have hlt := Finset.card_erase_lt_of_mem he
    omega

#print axioms solution
