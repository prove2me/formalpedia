-- Prove2me | solution 1 for MurtySimon.mem_Rt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:54.449433+00:00
-- url     : https://prove2.me/submissions/4fd1f30d-e35d-419d-9648-ae31620a31bb

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
theorem _root_.solution {f : Sym2 V} : f ∈ Rt G ↔ IsCrit G f := by simp [Rt]
end MurtySimon
