-- Prove2me | solution 1 for MatchingLogic.Necessity.C_not_backwardClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:44.938316+00:00
-- url     : https://prove2.me/submissions/cdaf730c-fc0f-461f-8c4b-fce0a9177779

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
namespace MatchingLogic.Necessity
theorem _root_.solution : ¬ M.BackwardClosed C := by
  intro h
  have h1 : (1 : Fin 3) ∈ C := h (show (0 : Fin 3) ∈ C from rfl) ⟨(), fun _ => 1, 0, by simp, rfl⟩
  exact absurd h1 (by decide)
end MatchingLogic.Necessity
