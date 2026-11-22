-- Prove2me | solution 1 for MatchingLogic.subset_localize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:25.288974+00:00
-- url     : https://prove2.me/submissions/19f7b853-5ca4-4751-b869-d0b1143a6edd

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (Γ : Set (Pattern S Var)) : Γ ⊆ localize Γ := by
  intro γ hγ
  exact ⟨γ, hγ, [], rfl⟩
end MatchingLogic
