-- Prove2me | solution 1 for MatchingLogic.finiteLocalCompleteness_of_finiteLocalModelExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:48.928668+00:00
-- url     : https://prove2.me/submissions/9d559ced-c4f6-4887-88b8-40f877c26b4b

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Theorems.Thm_MatchingLogic_countertheory_locConsistent_of_not_provable
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_denote_conj_eq_denoteSet_list
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_nt
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
theorem _root_.solution
    (hmodel : FiniteLocalModelExistence S Var) :
    FiniteLocalCompleteness S Var := by
  intro l phi hlocal
  by_contra hnot
  have hconsistent :
      LocConsistent {delta | delta ∈ [conj l, Pattern.nt phi]} :=
    countertheory_locConsistent_of_not_provable hnot
  obtain ⟨M, rho, u, hu⟩ := hmodel [conj l, Pattern.nt phi] hconsistent
  have hu' : ∀ delta ∈ [conj l, Pattern.nt phi], u ∈ M.denote rho delta := by
    simpa only [Model.denoteSet, Set.mem_iInter, Set.mem_ofPred_eq] using hu
  have huConj : u ∈ M.denote rho (conj l) := by
    exact hu' (conj l) (by simp)
  have huPremises : u ∈ M.denoteSet rho {delta | delta ∈ l} := by
    rwa [← M.denote_conj_eq_denoteSet_list]
  have huPhi : u ∈ M.denote rho phi := hlocal M rho huPremises
  have huNotPhi : u ∈ M.denote rho (Pattern.nt phi) := by
    exact hu' (Pattern.nt phi) (by simp)
  have hnotPhi : u ∉ M.denote rho phi := by
    simpa only [denote_nt, Set.mem_compl_iff] using huNotPhi
  exact hnotPhi huPhi
end MatchingLogic
