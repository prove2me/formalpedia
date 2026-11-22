-- Prove2me | solution 1 for MatchingLogic.canonicalExistence_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:14.70503+00:00
-- url     : https://prove2.me/submissions/da822b0f-c560-484b-b2ee-57030a539efe

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
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
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
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
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.mem_canonicalInterp



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
namespace MatchingLogic
theorem _root_.solution
    {sigma : S.Sym} {Gamma : CanonicalCarrier S}
    {phi : Fin (S.arity sigma) → Pattern S Nat}
    (harity : S.arity sigma = 0)
    (happ : Pattern.app sigma phi ∈ Gamma.val) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by
  let components : Fin (S.arity sigma) → CanonicalCarrier S := fun i =>
    Fin.elim0 (by simpa [harity] using i)
  refine ⟨components, ?_, ?_⟩
  · intro i
    exact Fin.elim0 (by simpa [harity] using i)
  · intro args _
    have hargs : args = phi := by
      funext i
      exact Fin.elim0 (by simpa [harity] using i)
    simpa [hargs] using happ
end MatchingLogic
