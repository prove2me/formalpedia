-- Prove2me | solution 1 for MatchingLogic.IsMCS.imp_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:14.769317+00:00
-- url     : https://prove2.me/submissions/01879295-d378-49a4-8b34-0a3569e45682

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_mp_mem
public import Theorems.Thm_MatchingLogic_IsMCS_neg_mem_iff_not_mem
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
variable {S : Signature}
namespace IsMCS
private theorem not_imp_taut :
    PForm.Taut
      (.imp (.imp (.atom 0) .bot) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem right_imp_taut :
    PForm.Taut (.imp (.atom 1) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
end IsMCS
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma)
    (p q : Pattern S Nat) :
    Pattern.imp p q ∈ Gamma ↔ p ∉ Gamma ∨ q ∈ Gamma := by
  constructor
  · intro himp
    by_cases hp : p ∈ Gamma
    · exact Or.inr (hM.mp_mem hp himp)
    · exact Or.inl hp
  · rintro (hnp | hq)
    · have hnpMem : Pattern.nt p ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnp
      have ht : Provable (∅ : Set (Pattern S Nat))
          (.imp (Pattern.nt p) (.imp p q)) := by
        simpa [PForm.subst, Pattern.nt] using
          (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
            (θ := fun n => if n = 0 then p else q) not_imp_taut)
      exact hM.mem_of_provable_imp hnpMem ht
    · have ht : Provable (∅ : Set (Pattern S Nat)) (.imp q (.imp p q)) := by
        simpa [PForm.subst] using
          (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
            (θ := fun n => if n = 0 then p else q) right_imp_taut)
      exact hM.mem_of_provable_imp hq ht
end MatchingLogic.IsMCS
