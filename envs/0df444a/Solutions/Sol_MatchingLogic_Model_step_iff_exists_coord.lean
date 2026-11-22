-- Prove2me | solution 1 for MatchingLogic.Model.step_iff_exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:13.800778+00:00
-- url     : https://prove2.me/submissions/5f8e0a91-1886-45a8-8009-a20d0286bf10

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Boxes

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type}
open MatchingLogic.Model
variable (M : Model S)
namespace MatchingLogic.Model
theorem _root_.solution (u v : M.carrier) :
    M.Step u v ↔ ∃ e : Coord S, M.stepAt e u v := by
  constructor
  · rintro ⟨σ, a, i, ha, hv⟩
    exact ⟨⟨σ, i⟩, a, ha, hv⟩
  · rintro ⟨⟨σ, i⟩, a, ha, hv⟩
    exact ⟨σ, a, i, ha, hv⟩
end MatchingLogic.Model
