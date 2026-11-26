-- Prove2me | solution 1 for MurtySimon.OnPath.mem_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:58.317139+00:00
-- url     : https://prove2.me/submissions/d692172a-89e7-48d5-bf5c-0b9ce5ffefce

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
namespace OnPath
theorem _root_.solution {e f : Sym2 V} (h : OnPath G e f) : e ∈ G.edgeSet := by
  obtain ⟨x, y, u, -, hm, rfl⟩ := h
  exact hm.2.2.1
end OnPath
end MurtySimon
