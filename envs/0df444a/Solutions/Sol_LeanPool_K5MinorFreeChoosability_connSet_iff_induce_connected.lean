-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.connSet_iff_induce_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:23.431191+00:00
-- url     : https://prove2.me/submissions/2ed57237-b4a5-4db7-ae6a-b7967cfd9a29

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_trans
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (G : SimpleGraph W) (s : Set W) :
    ConnSet G s ↔ (G.induce s).Connected := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    have : Nonempty s := ⟨⟨a, ha⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hxy := h x hx y hy
    have key : ∀ z, RIn G s x z → ∀ hz : z ∈ s,
        (G.induce s).Reachable ⟨x, hx⟩ ⟨z, hz⟩ := by
      intro z hz
      induction hz with
      | refl => exact fun _ => SimpleGraph.Reachable.refl _
      | @tail c d _ hcd ih =>
        intro hd
        exact (ih hcd.2.1).trans (SimpleGraph.Adj.reachable (by simpa using hcd.1))
    exact key y hxy hy
  · intro h
    obtain ⟨⟨a, ha⟩⟩ := h.nonempty
    refine ⟨⟨a, ha⟩, fun x hx y hy => ?_⟩
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (h.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
    have := Relation.ReflTransGen.lift (p := fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)
      Subtype.val (fun u v huv => ⟨by simpa using huv, u.2, v.2⟩) _ _ hr
    exact this
end LeanPool.K5MinorFreeChoosability
