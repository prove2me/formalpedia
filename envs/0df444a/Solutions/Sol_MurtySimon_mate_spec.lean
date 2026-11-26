-- Prove2me | solution 1 for MurtySimon.mate_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:14.413148+00:00
-- url     : https://prove2.me/submissions/39fd8b09-6915-4e9e-a5c3-e60dd924bf9e

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
theorem _root_.solution {x : V} (h : Covered M x) : s(x, mate M x) ∈ M := by
  have h' : ∃ y, s(x, y) ∈ M := h
  rw [mate, dif_pos h']; exact h'.choose_spec
end MurtySimon
