-- Prove2me | solution 1 for MurtySimon.OnPath.ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:27.131799+00:00
-- url     : https://prove2.me/submissions/12a2e811-4568-48f2-984c-0c6c6e244d25

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_IsMid_isCrit
public import Theorems.Thm_MurtySimon_IsCrit_not_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_isCrit

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
namespace OnPath
theorem _root_.solution {e f : Sym2 V} (h : OnPath G e f) : e ≠ f := by
  rintro rfl
  exact h.isCrit.not_mem_edgeSet h.mem_edgeSet
end OnPath
end MurtySimon
