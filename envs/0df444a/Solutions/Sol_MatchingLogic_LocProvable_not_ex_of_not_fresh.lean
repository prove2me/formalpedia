-- Prove2me | solution 1 for MatchingLogic.LocProvable.not_ex_of_not_fresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:28.749639+00:00
-- url     : https://prove2.me/submissions/d0fd5fb9-cf0e-447e-9156-4ae959467f95

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_Provable_swap_not
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
open Set
variable {S : Signature}
noncomputable section
private theorem not_mem_FV_conj {y : Nat} {l : List (Pattern S Nat)}
    (h : ∀ p ∈ l, y ∉ FV p) : y ∉ FV (conj l) := by
  induction l with
  | nil => simp [conj, Pattern.tp]
  | cons p l ih =>
      simp only [conj]
      simp [Pattern.and, Pattern.nt, h p (by simp), ih (by
        intro q hq
        exact h q (by simp [hq]))]
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
namespace LocProvable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {y : Nat} {q : Pattern S Nat}
    (hfresh : ∀ p ∈ Gamma, y ∉ FV p)
    (hnot : LocProvable Gamma (Pattern.nt q)) :
    LocProvable Gamma (Pattern.nt (.ex y q)) := by
  rcases hnot with ⟨l, hl, hp⟩
  have hswap : Provable (∅ : Set (Pattern S Nat))
      (.imp q (Pattern.nt (conj l))) := hp.swap_not
  have hfree : y ∉ FV (Pattern.nt (conj l)) := by
    simpa [Pattern.nt] using not_mem_FV_conj (y := y) (l := l) (by
      intro p hp
      exact hfresh p (hl p hp))
  have hgen : Provable (∅ : Set (Pattern S Nat))
      (.imp (.ex y q) (Pattern.nt (conj l))) := .exGen hswap hfree
  exact ⟨l, hl, hgen.swap_not⟩
end LocProvable
end MatchingLogic
