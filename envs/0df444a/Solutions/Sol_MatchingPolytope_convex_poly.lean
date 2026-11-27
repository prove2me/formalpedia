-- Prove2me | solution 1 for MatchingPolytope.convex_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:25.64891+00:00
-- url     : https://prove2.me/submissions/140997fe-a790-468e-9d15-7f8e2d686006

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V E : Type*}
namespace MatchingPolytope
theorem _root_.solution (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    Convex ℝ (Multi.Poly ends W F) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
  have hs : ∀ s : Finset E, ∑ e ∈ s, (a • x + b • y) e =
      a * ∑ e ∈ s, x e + b * ∑ e ∈ s, y e := by
    intro s
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp [hx0 e he, hy0 e he]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx1 e; have := hy1 e; positivity
  · rw [hs, hx2 v hv, hy2 v hv]; linarith
  · rw [hs]
    have h1 := hx3 S hS hodd
    have h2 := hy3 S hS hodd
    nlinarith
end MatchingPolytope
