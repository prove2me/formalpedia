-- Prove2me | solution 1 for NashWilliams.step_reachable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:10:13.453327+00:00
-- url     : https://prove2.me/submissions/9c81b28b-72d5-4462-a791-269c5d722b74

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_reachable_map_of_adj
public import Theorems.Thm_NashWilliams_adj_new
public import Theorems.Thm_NashWilliams_Step_uncov
public import Theorems.Thm_NashWilliams_reach_valid
public import Theorems.Thm_NashWilliams_reach_uncov_reachable

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
theorem _root_.solution {F F' : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) (hstep : Step G F F') (j : Fin k) (a b : V) :
    (F j ⊓ exchGraph G F₀).Reachable a b ↔ (F' j ⊓ exchGraph G F₀).Reachable a b := by
  classical
  have hF' : Relation.ReflTransGen (Step G) F₀ F' := hF.tail hstep
  have hval := (reach_valid hF₀ hF).1
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := hstep
  by_cases hj : j = i
  swap
  · simp only [update_of_ne hj]
  subst hj
  simp only [update_self]
  constructor
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    by_cases hc : s(c, d) = s(x, y)
    · have h := reach_uncov_reachable hF₀ hmax hF' (Step.uncov hval huv hxy) j
      simp only [update_self] at h
      rcases Sym2.eq_iff.1 hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
    · exact Adj.reachable
        ⟨Or.inl (deleteEdges_adj.2 ⟨hcd.1, fun h ↦ hc (Set.mem_singleton_iff.1 h)⟩), hcd.2⟩
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    rcases adj_new hcd.1 with h | h
    · exact Adj.reachable ⟨h.1, hcd.2⟩
    · have h' := reach_uncov_reachable hF₀ hmax hF huv j
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'
      · exact h'.symm
end NashWilliams
