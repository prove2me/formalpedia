-- Prove2me | solution 1 for MurtySimon.OnPath.isCrit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:57.301887+00:00
-- url     : https://prove2.me/submissions/17c03623-1b33-4445-bf88-436ca10d493d

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_IsMid_isCrit

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
namespace OnPath
theorem _root_.solution {e f : Sym2 V} (h : OnPath G e f) : IsCrit G f := by
  obtain ⟨x, y, u, rfl, hm, -⟩ := h
  exact hm.isCrit
end OnPath
end MurtySimon
