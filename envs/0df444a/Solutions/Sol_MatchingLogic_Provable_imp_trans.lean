-- Prove2me | solution 1 for MatchingLogic.Provable.imp_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:42.834799+00:00
-- url     : https://prove2.me/submissions/6a0a58e9-7de0-41a7-b3bf-6ac171995032

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] instDecidableEqPatternLocalTheory
private theorem taut_imp_trans :
    PForm.Taut (.imp (.imp (.atom 0) (.atom 1))
      (.imp (.imp (.atom 1) (.atom 2)) (.imp (.atom 0) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]
namespace LocProvable
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
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Var)}
    {phi psi chi : Pattern S Var} (h1 : Provable Gamma (.imp phi psi))
    (h2 : Provable Gamma (.imp psi chi)) : Provable Gamma (.imp phi chi) := by
  have ht : Provable Gamma
      (.imp (.imp phi psi) (.imp (.imp psi chi) (.imp phi chi))) := by
    exact .taut (θ := fun n => if n = 0 then phi else if n = 1 then psi else chi)
      taut_imp_trans
  exact .mp h2 (.mp h1 ht)
end Provable
end MatchingLogic
