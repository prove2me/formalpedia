-- Prove2me | solution 1 for MurtySimon.not_mem_of_mate_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:41.035378+00:00
-- url     : https://prove2.me/submissions/076b9016-d607-4b8f-9687-fd1f00614ef6

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
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
theorem _root_.solution {x y : V} (h : mate M x ≠ y) (hM : IsEdgeMatching G M) :
    s(x, y) ∉ M := fun hm => h (hM.mate_eq hm)
end MurtySimon
