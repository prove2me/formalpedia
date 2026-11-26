-- Prove2me | solution 1 for MurtySimon.IsEdgeMatching.adj_mate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:21.907777+00:00
-- url     : https://prove2.me/submissions/26500aed-03cb-4787-bb4b-2590ebf87d12

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
namespace IsEdgeMatching
theorem _root_.solution (hM : IsEdgeMatching G M) {x : V} (h : Covered M x) :
    G.Adj x (mate M x) :=
  hM.1 _ (mate_spec h)
end IsEdgeMatching
end MurtySimon
