-- Prove2me | solution 1 for MatchingLogic.IsMCS.or_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:28.727847+00:00
-- url     : https://prove2.me/submissions/3eefbc99-e99f-4c33-92be-7d89591598fa

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_Provable_or_intro_left
public import Theorems.Thm_MatchingLogic_Provable_or_intro_right
public import Theorems.Thm_MatchingLogic_LocProvable_of_provable
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_IsMCS_mem_iff_locProvable
public import Theorems.Thm_MatchingLogic_IsMCS_neg_mem_iff_not_mem
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
private theorem taut_not_or :
    PForm.Taut (.imp (.imp (.atom 0) .bot)
      (.imp (.imp (.atom 1) .bot)
        (.imp (.imp (.imp (.atom 0) .bot) (.atom 1)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem Provable.not_or {Gamma : Set (Pattern S Var)}
    (phi psi : Pattern S Var) :
    Provable Gamma
      (.imp (Pattern.nt phi) (.imp (Pattern.nt psi)
        (Pattern.nt (Pattern.or phi psi)))) := by
  simpa [PForm.subst, Pattern.nt, Pattern.or] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then phi else psi) taut_not_or)
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
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.or phi psi ∈ Gamma ↔ phi ∈ Gamma ∨ psi ∈ Gamma := by
  constructor
  · intro hor
    by_contra hneither
    have hnotphi : phi ∉ Gamma := fun hphi => hneither (Or.inl hphi)
    have hnotpsi : psi ∉ Gamma := fun hpsi => hneither (Or.inr hpsi)
    have hnphi : Pattern.nt phi ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnotphi
    have hnpsi : Pattern.nt psi ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnotpsi
    have hnotor : Pattern.nt (Pattern.or phi psi) ∈ Gamma := by
      have hstep : LocProvable Gamma
          (.imp (Pattern.nt psi) (Pattern.nt (Pattern.or phi psi))) :=
        (hM.mem_iff_locProvable.mp hnphi).mp
          (LocProvable.of_provable (Provable.not_or phi psi))
      exact hM.mem_iff_locProvable.mpr ((hM.mem_iff_locProvable.mp hnpsi).mp hstep)
    exact hM.1 ((hM.mem_iff_locProvable.mp hor).mp (hM.mem_iff_locProvable.mp hnotor))
  · intro h
    apply hM.mem_iff_locProvable.mpr
    rcases h with hphi | hpsi
    · exact (hM.mem_iff_locProvable.mp hphi).mp
        (LocProvable.of_provable (Provable.or_intro_left _ phi psi))
    · exact (hM.mem_iff_locProvable.mp hpsi).mp
        (LocProvable.of_provable (Provable.or_intro_right _ phi psi))
end MatchingLogic.IsMCS
