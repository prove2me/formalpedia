-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_poly_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:03.943956+00:00
-- url     : https://prove2.me/submissions/1f85099b-be22-4ff0-93ed-feefcc46999e

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_gcut_erase

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq E] {y : E → ℝ} (hy : y ∈ Poly ends W F) {e : E} (he0 : y e = 0) :
    y ∈ Poly ends W (F.erase e) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  refine ⟨fun e' he' => ?_, h1, fun v hv => ?_, fun S hS hodd => ?_⟩
  · by_cases h : e' = e
    · rw [h, he0]
    · exact h0 e' (fun h' => he' (Finset.mem_erase.2 ⟨h, h'⟩))
  · rw [gcut_erase, Finset.sum_erase _ he0]; exact h2 v hv
  · rw [gcut_erase, Finset.sum_erase _ he0]; exact h3 S hS hodd
end MatchingPolytope.Multi
