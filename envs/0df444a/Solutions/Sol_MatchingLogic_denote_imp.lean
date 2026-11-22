-- Prove2me | solution 1 for MatchingLogic.denote_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:31.749192+00:00
-- url     : https://prove2.me/submissions/f7d09e91-d3fd-4311-a1ff-82c97c00c74f

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
variable {S : Signature} {Var : Type} [DecidableEq Var] (M : Model S)
namespace MatchingLogic
theorem _root_.solution (ρ : Var → M.carrier) (φ ψ : Pattern S Var) :
    M.denote ρ (.imp φ ψ) = (M.denote ρ φ)ᶜ ∪ M.denote ρ ψ := rfl
end MatchingLogic
