-- Prove2me | solution 1 for MatchingPolytope.Multi.gw_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:42.939589+00:00
-- url     : https://prove2.me/submissions/9188ed92-d076-4345-85bf-69d80018ae0a

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_gw_left
public import Theorems.Thm_MatchingPolytope_Multi_gw_swap

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ g ∈ C, ∑ M, w1 M * chi M g = x g)
    (h2' : ∀ N, w2 N ≠ 0 → ∑ g ∈ C, chi N g = 1) (ψ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * ψ p.2 = ∑ N, w2 N * ψ N := by
  rw [← gw_left hx h1 h2' ψ]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => by rw [gw_swap]; rfl)
end MatchingPolytope.Multi
