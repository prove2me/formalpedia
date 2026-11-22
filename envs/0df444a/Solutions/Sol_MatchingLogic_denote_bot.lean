-- Prove2me | solution 1 for MatchingLogic.denote_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:29.772034+00:00
-- url     : https://prove2.me/submissions/9882285d-f49a-4f12-a930-198d200dc035

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
theorem _root_.solution (ρ : Var → M.carrier) :
    M.denote ρ (.bot : Pattern S Var) = ∅ := rfl
end MatchingLogic
