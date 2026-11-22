-- Prove2me | solution 1 for MatchingLogic.denote_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:28.275057+00:00
-- url     : https://prove2.me/submissions/2f02950c-2542-42b0-a725-f9d959ff126e

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
theorem _root_.solution (ρ : Var → M.carrier) (x : Var) :
    M.denote ρ (.var x) = {ρ x} := rfl
end MatchingLogic
