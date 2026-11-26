-- Prove2me | solution 1 for MurtySimon.IsEdgeMatching.mate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:47.383345+00:00
-- url     : https://prove2.me/submissions/8fdfa959-badb-4094-b276-299e43f2a93c

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec
public import Theorems.Thm_MurtySimon_IsEdgeMatching_eq_of_mem

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
theorem _root_.solution (hM : IsEdgeMatching G M) {x y : V} (h : s(x, y) ∈ M) :
    mate M x = y :=
  hM.eq_of_mem (mate_spec ⟨y, h⟩) h
end IsEdgeMatching
end MurtySimon
