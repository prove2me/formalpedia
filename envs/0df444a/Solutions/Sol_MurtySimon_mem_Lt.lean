-- Prove2me | solution 1 for MurtySimon.mem_Lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:05.27269+00:00
-- url     : https://prove2.me/submissions/40768be1-772a-4b61-8433-e3588043eb6f

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {e : Sym2 V} : e ∈ Lt G M ↔ e ∈ G.edgeSet ∧ e ∉ M := by
  simp [Lt]
end MurtySimon
