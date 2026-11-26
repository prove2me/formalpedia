-- Prove2me | solution 1 for MurtySimon.covered_mate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:23.433922+00:00
-- url     : https://prove2.me/submissions/fb4ffc05-0372-4d67-9590-490a61924584

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec

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
theorem _root_.solution {x : V} (h : Covered M x) : Covered M (mate M x) :=
  ⟨x, Sym2.eq_swap ▸ mate_spec h⟩
end MurtySimon
