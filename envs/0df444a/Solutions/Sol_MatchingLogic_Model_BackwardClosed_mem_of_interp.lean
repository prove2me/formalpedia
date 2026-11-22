-- Prove2me | solution 1 for MatchingLogic.Model.BackwardClosed.mem_of_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:19.958183+00:00
-- url     : https://prove2.me/submissions/f0d4d6d5-1ef0-4f44-ba3c-2c5a8188c41d

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Core

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
universe u
variable (S : Signature) (Var : Type)
attribute [instance] Model.nonempty
open MatchingLogic.Model
variable {S : Signature} (M : Model S)
namespace MatchingLogic.Model
namespace BackwardClosed
theorem _root_.solution {C : Set M.carrier} (hC : M.BackwardClosed C)
    {σ : S.Sym} {a : Fin (S.arity σ) → M.carrier} {u : M.carrier}
    (hu : u ∈ C) (ha : u ∈ M.interp σ a) (i : Fin (S.arity σ)) : a i ∈ C :=
  hC hu ⟨σ, a, i, ha, rfl⟩
end BackwardClosed
end MatchingLogic.Model
