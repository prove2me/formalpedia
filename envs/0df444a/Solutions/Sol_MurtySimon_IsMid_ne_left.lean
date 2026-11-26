-- Prove2me | solution 1 for MurtySimon.IsMid.ne_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:34.99495+00:00
-- url     : https://prove2.me/submissions/63f648dc-0645-4a9f-ab95-9c4aa3329a53

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
theorem _root_.solution {x y u : V} (h : IsMid G x y u) : u ≠ x := h.2.2.1.ne'
end IsMid
end MurtySimon
