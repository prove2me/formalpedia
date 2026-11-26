-- Prove2me | solution 1 for MurtySimon.one_le_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:27.840796+00:00
-- url     : https://prove2.me/submissions/2334a9aa-002c-4969-858a-fc21956f70bc

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
theorem _root_.solution (p : V × V) : 1 ≤ wt M p := by unfold wt; split_ifs <;> omega
end MurtySimon
