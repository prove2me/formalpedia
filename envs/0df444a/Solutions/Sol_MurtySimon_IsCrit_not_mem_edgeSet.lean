-- Prove2me | solution 1 for MurtySimon.IsCrit.not_mem_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:06.37198+00:00
-- url     : https://prove2.me/submissions/8ec0b7d0-fbed-45a0-afb4-e90a4cc4a9f8

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
namespace IsCrit
theorem _root_.solution {f : Sym2 V} (h : IsCrit G f) : f ∉ G.edgeSet := by
  obtain ⟨x, y, u, rfl, hm⟩ := h
  exact hm.2.1
end IsCrit
end MurtySimon
