-- Prove2me | solution 1 for MatchingLogic.LocProvable.and_intro
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:04.991452+00:00
-- url     : https://prove2.me/submissions/b980c637-eaee-4b00-9ed6-978b41e262bb

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
public import Theorems.Thm_MatchingLogic_Provable_imp_of
public import Theorems.Thm_MatchingLogic_Provable_and_elim_left
public import Theorems.Thm_MatchingLogic_Provable_and_elim_right
public import Theorems.Thm_MatchingLogic_Provable_imp_and
public import Theorems.Thm_MatchingLogic_LocProvable_mp
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
public import Theorems.Thm_MatchingLogic_provable_top
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] instDecidableEqPatternLocalTheory
namespace LocProvable
private theorem conj_append_left (l r : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var)) (.imp (conj (l ++ r)) (conj l)) := by
  induction l with
  | nil => simpa [conj] using (provable_top (∅ : Set (Pattern S Var))).imp_of
  | cons phi l ih =>
      apply Provable.imp_and
      · exact Provable.and_elim_left _ phi (conj (l ++ r))
      · exact (Provable.and_elim_right _ phi (conj (l ++ r))).imp_trans ih
private theorem conj_append_right (l r : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var)) (.imp (conj (l ++ r)) (conj r)) := by
  induction l with
  | nil => simpa using Provable.imp_refl (∅ : Set (Pattern S Var)) (conj r)
  | cons phi l ih =>
      exact (Provable.and_elim_right _ phi (conj (l ++ r))).imp_trans ih
end LocProvable
namespace IsMCS
end IsMCS
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.LocProvable
namespace MatchingLogic.LocProvable
theorem _root_.solution {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : LocProvable Gamma phi) (hpsi : LocProvable Gamma psi) :
    LocProvable Gamma (Pattern.and phi psi) := by
  rcases hphi with ⟨lphi, hlphi, hp⟩
  rcases hpsi with ⟨lpsi, hlpsi, hq⟩
  refine ⟨lphi ++ lpsi, ?_, ?_⟩
  · intro delta hdelta
    rcases List.mem_append.mp hdelta with hdelta | hdelta
    · exact hlphi delta hdelta
    · exact hlpsi delta hdelta
  · exact Provable.imp_and ((conj_append_left lphi lpsi).imp_trans hp)
      ((conj_append_right lphi lpsi).imp_trans hq)
end MatchingLogic.LocProvable
