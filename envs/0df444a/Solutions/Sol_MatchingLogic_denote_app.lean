-- Prove2me | solution 1 for MatchingLogic.denote_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:31.130467+00:00
-- url     : https://prove2.me/submissions/b48bec5b-e48c-4a0d-ab22-a4754930e492

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
theorem _root_.solution (ρ : Var → M.carrier) (σ : S.Sym)
    (f : Fin (S.arity σ) → Pattern S Var) :
    M.denote ρ (.app σ f) = M.app σ (fun i => M.denote ρ (f i)) := rfl
end MatchingLogic
