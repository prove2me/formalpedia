-- Prove2me | solution 1 for MurtySimon.completeBipartiteGraph_no_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:21:42.174347+00:00
-- url     : https://prove2.me/submissions/7462156e-714f-4e1d-b669-8ed5b718dbe2

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution {A B : Type*} {p q w : A ⊕ B}
    (hpq : (completeBipartiteGraph A B).Adj p q) (hpw : (completeBipartiteGraph A B).Adj p w)
    (hwq : (completeBipartiteGraph A B).Adj w q) : False := by
  rcases p with p | p <;> rcases q with q | q <;> rcases w with w | w <;> simp_all
end MurtySimon
