-- Prove2me | solution 1 for MurtySimon.IsMid.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:04.322961+00:00
-- url     : https://prove2.me/submissions/741f2d91-093c-4e0a-80ac-f61757ad20d3

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
theorem _root_.solution {x y u u' : V} (h : IsMid G x y u) (h' : IsMid G x y u') : u' = u :=
  h.2.2.2.2 u' h'.2.2.1 h'.2.2.2.1
end IsMid
end MurtySimon
