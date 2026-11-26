-- Prove2me | solution 1 for MurtySimon.IsMid.isCrit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:54.173944+00:00
-- url     : https://prove2.me/submissions/8c35a0f9-6e59-42df-ac79-9fa0e5377730

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
theorem _root_.solution {x y u : V} (h : IsMid G x y u) : IsCrit G s(x, y) := ⟨x, y, u, rfl, h⟩
end IsMid
end MurtySimon
