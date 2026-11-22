-- Prove2me | solution 1 for MatchingLogic.countertheory_locConsistent_of_not_provable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:58.450392+00:00
-- url     : https://prove2.me/submissions/03ff1e92-d899-4f2f-b5c5-8b3e8af4c4cb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Theorems.Thm_MatchingLogic_locProvable_empty_iff
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_deduction_insert
public import Theorems.Thm_MatchingLogic_LocProvable_mp
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
private theorem countertheory_taut :
    PForm.Taut
      (.imp
        (.imp (.imp (.atom 0) .bot) (.imp (.atom 1) .bot))
        (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    {l : List (Pattern S Var)} {phi : Pattern S Var}
    (hnot : ¬ Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)) :
    LocConsistent {delta | delta ∈ [conj l, Pattern.nt phi]} := by
  intro hbot
  have hbot' : LocProvable
      (insert (conj l) (insert (Pattern.nt phi) (∅ : Set (Pattern S Var))))
      (.bot : Pattern S Var) := by
    have hset : {delta : Pattern S Var | delta ∈ [conj l, Pattern.nt phi]} =
        insert (conj l) (insert (Pattern.nt phi) (∅ : Set (Pattern S Var))) := by
      ext delta
      simp
    rwa [← hset]
  have hfirst : LocProvable (insert (Pattern.nt phi) (∅ : Set (Pattern S Var)))
      (.imp (conj l) .bot) := hbot'.deduction_insert
  have hsecond : LocProvable (∅ : Set (Pattern S Var))
      (.imp (Pattern.nt phi) (.imp (conj l) .bot)) := hfirst.deduction_insert
  have hordinary : Provable (∅ : Set (Pattern S Var))
      (.imp (Pattern.nt phi) (.imp (conj l) .bot)) := locProvable_empty_iff.mp hsecond
  have hclassical : Provable (∅ : Set (Pattern S Var))
      (.imp (.imp (Pattern.nt phi) (.imp (conj l) .bot)) (.imp (conj l) phi)) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Var)))
        (θ := fun n => if n = 0 then phi else conj l) countertheory_taut)
  exact hnot (Provable.mp hordinary hclassical)
end MatchingLogic
