-- Prove2me | solution 1 for MatchingPolytope.Multi.chi_mem_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:49.908606+00:00
-- url     : https://prove2.me/submissions/f68d136e-15a4-4c83-9b19-2a23f25168b9

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_sum_chi_gcut
public import Theorems.Thm_MatchingPolytope_Multi_card_gcut_odd

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) :
    chi M ∈ Poly ends W F := by
  refine ⟨fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp only [chi, ite_eq_right_iff]; exact fun h => absurd (hM.1 h) he
  · simp only [chi]; split_ifs <;> norm_num
  · rw [sum_chi_gcut hM.1, hM.2 v hv]; simp
  · rw [sum_chi_gcut hM.1]
    have := (card_gcut_odd hV hM hS hodd).pos
    exact_mod_cast this
end MatchingPolytope.Multi
