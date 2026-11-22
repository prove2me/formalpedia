-- Prove2me | solution 1 for MatchingLogic.denote_tp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:03.411023+00:00
-- url     : https://prove2.me/submissions/eee2075d-a8fa-449f-87fc-d1744341b427

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
theorem _root_.solution (ρ : Var → M.carrier) :
    M.denote ρ (Pattern.tp : Pattern S Var) = Set.univ := by
  simp [Pattern.tp]
end MatchingLogic
