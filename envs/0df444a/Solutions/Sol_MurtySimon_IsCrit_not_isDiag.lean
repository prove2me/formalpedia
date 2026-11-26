-- Prove2me | solution 1 for MurtySimon.IsCrit.not_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:39.219804+00:00
-- url     : https://prove2.me/submissions/6cc892cb-f571-4a5f-9540-45ad41770593

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
theorem _root_.solution {f : Sym2 V} (h : IsCrit G f) : ¬ f.IsDiag := by
  obtain ⟨x, y, u, rfl, hm⟩ := h
  simpa using hm.1
end IsCrit
end MurtySimon
