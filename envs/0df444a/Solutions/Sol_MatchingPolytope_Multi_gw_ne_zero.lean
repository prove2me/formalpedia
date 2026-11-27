-- Prove2me | solution 1 for MatchingPolytope.Multi.gw_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:02.736903+00:00
-- url     : https://prove2.me/submissions/2a741487-9506-4e9c-9122-f0b7dc2d78b8

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_chi_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution {C : Finset E} {x : E → ℝ} {w1 w2 : Finset E → ℝ} {p : Finset E × Finset E}
    (h : gw C x w1 w2 p ≠ 0) :
    ∃ g ∈ C, g ∈ p.1 ∧ g ∈ p.2 ∧ w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 := by
  obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨g, hg, chi_ne_zero ?_, chi_ne_zero ?_, ?_, ?_⟩ <;> intro h0 <;> apply hne <;>
    simp [h0]
end MatchingPolytope.Multi
