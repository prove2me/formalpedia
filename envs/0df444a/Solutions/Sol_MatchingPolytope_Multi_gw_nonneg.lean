-- Prove2me | solution 1 for MatchingPolytope.Multi.gw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:02.646187+00:00
-- url     : https://prove2.me/submissions/48d73908-7b19-4b36-b26c-ba28a5c9b16c

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_chi_nonneg

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, 0 < x g) {w1 w2 : Finset E → ℝ}
    (h1 : ∀ M, 0 ≤ w1 M) (h2 : ∀ M, 0 ≤ w2 M) (p : Finset E × Finset E) :
    0 ≤ gw C x w1 w2 p := by
  unfold gw
  apply Finset.sum_nonneg
  intro g hg
  have := hx g hg
  have := chi_nonneg p.1 g
  have := chi_nonneg p.2 g
  have := h1 p.1
  have := h2 p.2
  positivity
end MatchingPolytope.Multi
