-- Prove2me | solution 1 for MatchingLogic.Pattern.FV_subset_allVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:00.785803+00:00
-- url     : https://prove2.me/submissions/da1a1cc8-1b6e-44eb-a9cb-53c24163d99b

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
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
namespace MatchingLogic.Pattern
theorem _root_.solution (p : Pattern S Var) : FV p ⊆ ↑p.allVars := by
  induction p with
  | var x => simp [allVars]
  | bot => simp [allVars]
  | app sigma args ih =>
      intro x hx
      simp only [FV_app, Set.mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ih i hi⟩
  | imp phi psi ihphi ihpsi =>
      intro x hx
      rcases hx with hx | hx
      · exact Finset.mem_union_left _ (ihphi hx)
      · exact Finset.mem_union_right _ (ihpsi hx)
  | ex x phi ih =>
      intro y hy
      exact Finset.mem_insert_of_mem (ih hy.1)
end MatchingLogic.Pattern
