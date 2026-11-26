-- Prove2me | solution 1 for MurtySimon.IsEdgeMatching.mate_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:37.641404+00:00
-- url     : https://prove2.me/submissions/2ba70973-48cb-4704-bede-e5077a081c29

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsEdgeMatching_adj_mate

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
    mate M x ≠ x :=
  (hM.adj_mate h).ne'
end IsEdgeMatching
end MurtySimon
