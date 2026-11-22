-- Prove2me | solution 1 for MatchingLogic.LocProvable.provable_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:23.984965+00:00
-- url     : https://prove2.me/submissions/5881aa1c-4e8c-4ae5-810b-f460aa0c1762

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
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
namespace LocProvable
theorem _root_.solution {p : Pattern S Nat}
    (h : LocProvable (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by
  rcases h with ⟨l, hl, hp⟩
  have hnil : l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    exact (hl q hq).elim
  subst l
  exact Provable.mp (provable_top (∅ : Set (Pattern S Nat))) (by
    simpa [conj] using hp)
end LocProvable
end MatchingLogic
