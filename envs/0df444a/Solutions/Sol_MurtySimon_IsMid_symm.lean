-- Prove2me | solution 1 for MurtySimon.IsMid.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:42.880148+00:00
-- url     : https://prove2.me/submissions/cb9e5dc5-367d-4354-a7be-2d9a362f7c81

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
theorem _root_.solution {x y u : V} (h : IsMid G x y u) : IsMid G y x u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, fun h => h2 h.symm, h4.symm, h3.symm, fun w hw1 hw2 => h5 w hw2.symm hw1.symm⟩
end IsMid
end MurtySimon
