-- Prove2me | solution 1 for MatchingLogic.IsMCS.singleton_argument_locConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:23.085865+00:00
-- url     : https://prove2.me/submissions/3e0307d5-53f7-482f-adef-0c5cef5c206e

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_LocProvable_provable_empty
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_LocProvable_deduction_insert
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
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


attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.canonicalModel_interp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution
    {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma)
    {sigma : S.Sym} {args : Fin (S.arity sigma) → Pattern S Nat}
    (happ : Pattern.app sigma args ∈ Gamma) (i : Fin (S.arity sigma)) :
    LocConsistent ({args i} : Set (Pattern S Nat)) := by
  intro hbad
  have hbad' : LocProvable
      (insert (args i) (∅ : Set (Pattern S Nat))) (.bot : Pattern S Nat) := by
    simpa only [insert_empty_eq] using hbad
  have hargbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (args i) .bot) :=
    (LocProvable.deduction_insert hbad').provable_empty
  have hframe : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args) (.app sigma (Function.update args i .bot))) := by
    have h := Provable.framing (Γ := (∅ : Set (Pattern S Nat)))
      (σ := sigma) (i := i) (args := args) hargbot
    simpa only [Function.update_eq_self] using h
  have hprop : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma (Function.update args i .bot)) .bot) :=
    Provable.propBot
  have happbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args) .bot) := hframe.imp_trans hprop
  have hbot : (.bot : Pattern S Nat) ∈ Gamma :=
    hM.mem_of_provable_imp happ happbot
  exact hM.1 (LocProvable.of_mem hbot)
end IsMCS
end MatchingLogic
