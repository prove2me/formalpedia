-- Prove2me | solution 1 for MatchingLogic.LocProvable.deduction_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:56.007119+00:00
-- url     : https://prove2.me/submissions/87f75eaa-baaa-4e18-a3bb-6acba3ef925c

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
public import Theorems.Thm_MatchingLogic_Provable_imp_of
public import Theorems.Thm_MatchingLogic_Provable_and_elim_left
public import Theorems.Thm_MatchingLogic_Provable_and_elim_right
public import Theorems.Thm_MatchingLogic_LocProvable_mp
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] instDecidableEqPatternLocalTheory
private theorem taut_imp_of :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem taut_imp_imp_trans :
    PForm.Taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.imp (.atom 2) (.atom 3))
        (.imp (.atom 0) (.imp (.atom 1) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]
private theorem Provable.imp_imp_trans {Gamma : Set (Pattern S Var)}
    {alpha beta gamma delta : Pattern S Var}
    (h1 : Provable Gamma (.imp alpha (.imp beta gamma)))
    (h2 : Provable Gamma (.imp gamma delta)) :
    Provable Gamma (.imp alpha (.imp beta delta)) := by
  have ht : Provable Gamma
      (.imp (.imp alpha (.imp beta gamma))
        (.imp (.imp gamma delta) (.imp alpha (.imp beta delta)))) := by
    exact .taut (θ := fun n =>
      if n = 0 then alpha else if n = 1 then beta else if n = 2 then gamma else delta)
      taut_imp_imp_trans
  exact .mp h2 (.mp h1 ht)
private theorem taut_imp_imp_and :
    PForm.Taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 3)))
        (.imp (.atom 0) (.imp (.atom 1)
          (.imp (.imp (.atom 2) (.imp (.atom 3) .bot)) .bot))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]
private theorem Provable.imp_imp_and {Gamma : Set (Pattern S Var)}
    {alpha beta gamma delta : Pattern S Var}
    (h1 : Provable Gamma (.imp alpha (.imp beta gamma)))
    (h2 : Provable Gamma (.imp alpha (.imp beta delta))) :
    Provable Gamma (.imp alpha (.imp beta (Pattern.and gamma delta))) := by
  have ht : Provable Gamma
      (.imp (.imp alpha (.imp beta gamma))
        (.imp (.imp alpha (.imp beta delta))
          (.imp alpha (.imp beta (Pattern.and gamma delta))))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n =>
          if n = 0 then alpha else if n = 1 then beta else if n = 2 then gamma else delta)
        taut_imp_imp_and)
  exact .mp h2 (.mp h1 ht)
namespace LocProvable
private theorem filter_imp_conj (phi : Pattern S Var) (l : List (Pattern S Var)) :
    Provable (∅ : Set (Pattern S Var))
      (.imp (conj (l.filter (fun delta => decide (delta ≠ phi)))) (.imp phi (conj l))) := by
  classical
  induction l with
  | nil =>
      simpa [conj] using ((provable_top (∅ : Set (Pattern S Var))).imp_of).imp_of
  | cons delta l ih =>
      by_cases hdelta : delta = phi
      · subst delta
        simpa [conj] using (Provable.imp_imp_and (Provable.imp_refl _ _ |>.imp_of) ih)
      · let tail := conj (l.filter fun eta => decide (eta ≠ phi))
        have hleft : Provable (∅ : Set (Pattern S Var))
            (.imp (Pattern.and delta tail) (.imp phi delta)) :=
          (Provable.and_elim_left _ delta tail).imp_trans
            (Provable.taut (θ := fun n => if n = 0 then delta else phi) taut_imp_of)
        have hright : Provable (∅ : Set (Pattern S Var))
            (.imp (Pattern.and delta tail) (.imp phi (conj l))) :=
          (Provable.and_elim_right _ delta tail).imp_trans ih
        simpa [tail, hdelta, conj] using Provable.imp_imp_and hleft hright
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
open MatchingLogic.LocProvable
namespace MatchingLogic.LocProvable
theorem _root_.solution {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (h : LocProvable (insert phi Gamma) psi) : LocProvable Gamma (.imp phi psi) := by
  classical
  rcases h with ⟨l, hl, hp⟩
  refine ⟨l.filter (fun delta => decide (delta ≠ phi)), ?_, ?_⟩
  · intro delta hdelta
    have hlin : delta ∈ l := (List.mem_filter.mp hdelta).1
    have hne : delta ≠ phi := of_decide_eq_true (List.mem_filter.mp hdelta).2
    rcases hl delta hlin with hEq | hGamma
    · exact False.elim (hne hEq)
    · exact hGamma
  · exact (filter_imp_conj phi l).imp_imp_trans hp
end MatchingLogic.LocProvable
