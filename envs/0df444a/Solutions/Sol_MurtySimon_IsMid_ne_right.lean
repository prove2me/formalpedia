-- Prove2me | solution 1 for MurtySimon.IsMid.ne_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:35.841968+00:00
-- url     : https://prove2.me/submissions/3076401f-b600-4773-a0e5-905e97ea3e5a

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
namespace IsMid
theorem _root_.solution {x y u : V} (h : IsMid G x y u) : u ≠ y := h.2.2.2.1.ne
end IsMid
end MurtySimon
