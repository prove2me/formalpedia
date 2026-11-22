-- Prove2me | solution 1 for MatchingLogic.pointedTheory_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:19.155895+00:00
-- url     : https://prove2.me/submissions/308acf20-9f06-426e-a568-69c49c15b9e9

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_nt
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_soundness
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
noncomputable section
variable {S : Signature}
private theorem pointedTheory_mem_denote_conj (M : Model S)
    (rho : Nat → M.carrier) (u : M.carrier)
    (l : List (Pattern S Nat))
    (hl : ∀ p ∈ l, u ∈ M.denote rho p) :
    u ∈ M.denote rho (conj l) := by
  induction l with
  | nil => simp [conj]
  | cons p l ih =>
      have hp := hl p (by simp)
      have htail := ih (by
        intro q hq
        exact hl q (by simp [hq]))
      simpa [conj, Pattern.and, Pattern.nt] using And.intro hp htail
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution (M : Model S) (rho : Nat → M.carrier)
    (u : M.carrier) : IsMCS (pointedTheory M rho u) := by
  constructor
  · rintro ⟨l, hl, hp⟩
    have hconj : u ∈ M.denote rho (conj l) :=
      pointedTheory_mem_denote_conj M rho u l (by
        intro p hp'
        exact hl p hp')
    have htotal := soundness (∅ : Set (Pattern S Nat))
      (.imp (conj l) .bot) hp M (by simp [Model.SatSet]) rho
    have himp : u ∈ M.denote rho (.imp (conj l) .bot) := by
      rw [htotal]
      exact Set.mem_univ u
    simp only [denote_imp, denote_bot, Set.union_empty, Set.mem_compl_iff] at himp
    exact himp hconj
  · intro Delta hstrict hDeltaConsistent
    obtain ⟨p, hpDelta, hpNotGamma⟩ := Set.exists_of_ssubset hstrict
    have hnotpGamma : Pattern.nt p ∈ pointedTheory M rho u := by
      change u ∈ M.denote rho (Pattern.nt p)
      change u ∉ M.denote rho p at hpNotGamma
      simpa only [denote_nt, Set.mem_compl_iff] using hpNotGamma
    have hpLoc : LocProvable Delta p := LocProvable.of_mem hpDelta
    have hnotpLoc : LocProvable Delta (Pattern.nt p) :=
      LocProvable.of_mem (hstrict.1 hnotpGamma)
    exact hDeltaConsistent (hpLoc.mp hnotpLoc)
end MatchingLogic
