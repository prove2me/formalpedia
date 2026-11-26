-- Prove2me | solution 1 for MurtySimon.emb_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:33.441993+00:00
-- url     : https://prove2.me/submissions/98f68ba7-3141-40a2-a07b-03805e71cf9b

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (M : Finset (Sym2 V)) (v : Sym2 V) :
    emb G M ((aux G M).connectedComponentMk v) = (aux G ∅).connectedComponentMk v := rfl
end MurtySimon
