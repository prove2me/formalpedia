-- Prove2me | solution 1 for MatchingPolytope.convex_matchingPolytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:27.424173+00:00
-- url     : https://prove2.me/submissions/1ffe12c9-71ab-47f7-96d3-aab5c96127e4

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution : Convex ℝ (matchingPolytope G) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hs : ∀ s : Finset G.edgeSet, ∑ e ∈ s, (a • x + b • y) e =
      a * ∑ e ∈ s, x e + b * ∑ e ∈ s, y e := by
    intro s
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun e => ?_, fun v => ?_, fun S hS => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx1 e; have := hy1 e; positivity
  · rw [hs]
    have := hx2 v; have := hy2 v
    nlinarith
  · rw [hs]
    have h1 := hx3 S hS
    have h2 := hy3 S hS
    have : a * ∑ e ∈ innerEdges G S, x e + b * ∑ e ∈ innerEdges G S, y e ≤
        a * (((S.card : ℝ) - 1) / 2) + b * (((S.card : ℝ) - 1) / 2) := by
      gcongr
    rw [← add_mul, hab, one_mul] at this
    exact this
end MatchingPolytope
