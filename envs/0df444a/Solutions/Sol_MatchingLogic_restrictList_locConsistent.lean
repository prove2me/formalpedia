-- Prove2me | solution 1 for MatchingLogic.restrictList_locConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:48.516672+00:00
-- url     : https://prove2.me/submissions/1941b37a-885e-4806-8e61-99ef103ce220

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_restrictList
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_conj
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Provable_liftSignature
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
theorem _root_.solution [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern S Var)) (hsupport : ∀ p ∈ l, p.symbolSupport ⊆ F)
    (hconsistent : LocConsistent {delta | delta ∈ l}) :
    LocConsistent {delta | delta ∈ Pattern.restrictList F l hsupport} := by
  intro hbad
  apply hconsistent
  rcases hbad with ⟨k, hk, hp⟩
  refine ⟨k.map (Pattern.liftSignature F), ?_, ?_⟩
  · intro delta hdelta
    rcases List.mem_map.mp hdelta with ⟨q, hq, rfl⟩
    have hq' := hk q hq
    change q ∈ Pattern.restrictList F l hsupport at hq'
    have hlift : q.liftSignature F ∈ l := by
      have hmem : q.liftSignature F ∈
          (Pattern.restrictList F l hsupport).map (Pattern.liftSignature F) :=
        List.mem_map.mpr ⟨q, hq', rfl⟩
      rwa [Pattern.liftSignature_restrictList] at hmem
    exact hlift
  · have hp' := hp.liftSignature F
    simpa [Pattern.liftSignature, Pattern.liftSignature_conj] using hp'
end MatchingLogic
