-- Prove2me | solution 1 for MatchingLogic.denote_nt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:10.27085+00:00
-- url     : https://prove2.me/submissions/2afbf62e-ccfd-4c89-bebd-23a487cfc39b

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
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_ex
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_ex

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
universe u
variable (S : Signature) (Var : Type)
attribute [instance] Model.nonempty
variable {S : Signature} {Var : Type} [DecidableEq Var] (M : Model S)
namespace MatchingLogic
theorem _root_.solution (ρ : Var → M.carrier) (φ : Pattern S Var) :
    M.denote ρ φ.nt = (M.denote ρ φ)ᶜ := by
  simp [Pattern.nt]
end MatchingLogic
