-- Prove2me | solution 1 for MatchingLogic.Pattern.captureFree_liftSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:14.151887+00:00
-- url     : https://prove2.me/submissions/20b732c0-2130-4c78-b62d-654126c8d8f7

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Theorems.Thm_MatchingLogic_Pattern_FV_liftSignature
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
omit [DecidableEq Var]
namespace MatchingLogic.Pattern
theorem _root_.solution [DecidableEq S.Sym] (F : Finset S.Sym)
    {x y : Var} {p : Pattern (S.restrict F) Var} :
    CaptureFree x y p → CaptureFree x y (p.liftSignature F) := by
  intro h
  induction p generalizing x y with
  | var z => trivial
  | bot => trivial
  | app sigma args ih =>
      intro i
      exact ih i (h i)
  | imp phi psi ihphi ihpsi => exact ⟨ihphi h.1, ihpsi h.2⟩
  | ex z phi ih =>
      rcases h with hzx | hfree | ⟨hzy, hrec⟩
      · exact Or.inl hzx
      · exact Or.inr (Or.inl (by simpa [FV_liftSignature] using hfree))
      · exact Or.inr (Or.inr ⟨hzy, ih hrec⟩)
end MatchingLogic.Pattern
