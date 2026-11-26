-- Prove2me | solution 1 for MurtySimon.IsEdgeMatching.mate_mate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:59.644904+00:00
-- url     : https://prove2.me/submissions/9e17017c-962c-4d74-b134-9fb04b4c5c59

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec
public import Theorems.Thm_MurtySimon_IsEdgeMatching_mate_eq

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
    mate M (mate M x) = x :=
  hM.mate_eq (Sym2.eq_swap ▸ mate_spec h)
end IsEdgeMatching
end MurtySimon
