-- Prove2me | solution 1 for MurtySimon.isEdgeMatching_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:09.972883+00:00
-- url     : https://prove2.me/submissions/3018243b-b5c4-4fc5-a600-4804894f6edd

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {e : Sym2 V} (he : e ∈ G.edgeSet) : IsEdgeMatching G {e} := by
  refine ⟨fun f hf => mem_singleton.1 hf ▸ he, fun f hf g hg hfg => ?_⟩
  rw [mem_singleton.1 hf, mem_singleton.1 hg] at hfg
  exact absurd rfl hfg
end MurtySimon
