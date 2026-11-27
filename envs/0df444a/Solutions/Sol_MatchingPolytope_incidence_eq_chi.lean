-- Prove2me | solution 1 for MatchingPolytope.incidence_eq_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:34.727194+00:00
-- url     : https://prove2.me/submissions/440c5e58-f8ed-468a-bb65-70ca08903656

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_mem_edgesOf

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution (M : G.Subgraph) : incidence G M = chi (edgesOf G M) := by
  funext e
  unfold incidence chi
  split_ifs with h1 h2 h2 <;> simp_all [mem_edgesOf]
end MatchingPolytope
