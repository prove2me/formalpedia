-- Prove2me | solution 1 for MatchingLogic.denote_ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:32.429797+00:00
-- url     : https://prove2.me/submissions/64eccc12-5b27-4da4-8f55-c06e55004f14

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
theorem _root_.solution (ρ : Var → M.carrier) (x : Var) (φ : Pattern S Var) :
    M.denote ρ (.ex x φ) = ⋃ a : M.carrier, M.denote (Function.update ρ x a) φ := rfl
end MatchingLogic
