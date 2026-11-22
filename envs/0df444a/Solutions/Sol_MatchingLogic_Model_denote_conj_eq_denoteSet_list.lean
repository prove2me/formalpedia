-- Prove2me | solution 1 for MatchingLogic.Model.denote_conj_eq_denoteSet_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:55.943004+00:00
-- url     : https://prove2.me/submissions/c8a79d11-e4d9-4c0c-ae1e-353c5ce5f939

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
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
namespace MatchingLogic
namespace Model
theorem _root_.solution (M : Model S)
    (rho : Var → M.carrier) (l : List (Pattern S Var)) :
    M.denote rho (conj l) = M.denoteSet rho {delta | delta ∈ l} := by
  induction l with
  | nil =>
      simp [conj, MatchingLogic.Model.denoteSet]
  | cons delta l ih =>
      ext u
      simp [conj, Pattern.and, Pattern.nt, ih, MatchingLogic.Model.denoteSet]
end Model
end MatchingLogic
