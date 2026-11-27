-- Prove2me | solution 1 for MatchingPolytope.Multi.sum_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:00.448352+00:00
-- url     : https://prove2.me/submissions/04c3b3d3-ca07-47c9-9200-1b0cec8ce96b

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (s : Finset E) (y d : E → ℝ) (ε : ℝ) :
    ∑ e ∈ s, (y + ε • d) e = ∑ e ∈ s, y e + ε * ∑ e ∈ s, d e := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]
end MatchingPolytope.Multi
