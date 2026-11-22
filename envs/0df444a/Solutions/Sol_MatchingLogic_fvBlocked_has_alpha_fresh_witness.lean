-- Prove2me | solution 1 for MatchingLogic.fvBlocked_has_alpha_fresh_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:48.756702+00:00
-- url     : https://prove2.me/submissions/11d53329-2294-419e-a361-1047c0746c7a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
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
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_Provable_weaken_empty
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_completedModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_mem_completedInterp
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
public import Theorems.Thm_MatchingLogic_provable_top
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_nat
attribute [local simp] MatchingLogic.AppCtx.plug_comp
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
attribute [local simp] MatchingLogic.Pattern.rename_comp
attribute [local simp] MatchingLogic.Pattern.rename_id
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.completedModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_completedInterp
attribute [local simp] MatchingLogic.mem_generatedInterp


section
@[expose] public section
namespace MatchingLogic
open Set
noncomputable section
private theorem provable_empty_of_local_valid {S : Signature}
    {p : Pattern S Nat} (h : LocalCons (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by
  obtain ⟨l, hl, hp⟩ := strongLocalCompleteness_nat
    (∅ : Set (Pattern S Nat)) p h
  have hempty : l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    exact (hl q hq).elim
  subst l
  exact Provable.mp (provable_top (∅ : Set (Pattern S Nat)))
    (by simpa [conj] using hp)
private theorem alphaEq_of_denote_eq {S : Signature}
    {p q : Pattern S Nat}
    (hden : ∀ (M : Model S) (rho : Nat → M.carrier),
      M.denote rho p = M.denote rho q)
    (hcomplexity : p.complexity = q.complexity) :
    Pattern.AlphaEq p q := by
  refine ⟨?_, ?_, hcomplexity⟩
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp p q) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hp : u ∈ M.denote rho p
    · exact Or.inr (by simpa [hden M rho] using hp)
    · exact Or.inl hp
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp q p) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hq : u ∈ M.denote rho q
    · exact Or.inr (by simpa [hden M rho] using hq)
    · exact Or.inl hq
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
namespace MatchingLogic
theorem _root_.solution :
    ∃ (x' : Nat) (p' : Pattern WitnessCollapseSig Nat) (y : Nat),
      Pattern.AlphaEq
        (.ex 1 (Pattern.and (.var 1) (.var 0))) (.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ witnessCollapseTheory := by
  let p' : Pattern WitnessCollapseSig Nat :=
    Pattern.and (.var 0) (.var 0)
  refine ⟨1, p', 1, ?_, ?_, ?_⟩
  · apply alphaEq_of_denote_eq
    · intro M rho
      ext u
      simp [p', Pattern.and, Pattern.nt]
    · simp [p', Pattern.complexity]
  · simp [p', Pattern.allVars]
  · change true ∈ witnessCollapseModel.denote witnessCollapseRho _
    simp [p', Pattern.captureAvoidingSubst, Pattern.avoidBinder,
      Pattern.and, Pattern.nt, witnessCollapseRho]
end MatchingLogic
