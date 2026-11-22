-- Prove2me | solution 1 for MatchingLogic.alphaWitnessTheory_not_alphaFreshWitnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:22.942706+00:00
-- url     : https://prove2.me/submissions/acbe0a44-e8d9-49be-ad23-f8a7dc68c19f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
public import Theorems.Thm_MatchingLogic_pairArgs_zero
public import Theorems.Thm_MatchingLogic_pairArgs_one
public import Theorems.Thm_MatchingLogic_alphaWitnessTheory_isMCS
public import Theorems.Thm_MatchingLogic_alphaBlocked_mem
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
public import Theorems.Thm_MatchingLogic_IsMCS_alphaEq_mem_iff
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_denote_eq
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_complexity_eq
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
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


attribute [local simp] MatchingLogic.pairArgs_zero
attribute [local simp] MatchingLogic.pairArgs_one
section
@[expose] public section
namespace MatchingLogic
open Set
noncomputable section
@[simp] private theorem boolPair_zero (p q : Bool) : boolPair p q 0 = p := rfl
@[simp] private theorem boolPair_one (p q : Bool) : boolPair p q 1 = q := rfl
private theorem alphaWitness_complexity_pos
    (p : Pattern AlphaWitnessSig Nat) : 0 < p.complexity := by
  cases p with
  | var => simp [Pattern.complexity]
  | bot => simp [Pattern.complexity]
  | app sigma args => simp [Pattern.complexity]
  | imp p q => simp [Pattern.complexity]
  | ex x p => simp [Pattern.complexity]
private theorem alphaWitness_complexity_one
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 1) :
    (∃ z, p = .var z) ∨ p = .bot := by
  cases p with
  | var z => exact Or.inl ⟨z, rfl⟩
  | bot => exact Or.inr rfl
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      simp [Pattern.complexity] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex x p =>
      have hp := alphaWitness_complexity_pos p
      simp [Pattern.complexity] at h
      omega
private theorem alphaWitness_complexity_two
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 2) :
    ∃ z q, p = .ex z q ∧ ((∃ a, q = .var a) ∨ q = .bot) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      cases sigma
      rw [Pattern.complexity, Fin.sum_univ_two] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex z q =>
      have hq : q.complexity = 1 := by
        simp [Pattern.complexity] at h
        omega
      exact ⟨z, q, rfl, alphaWitness_complexity_one q hq⟩
private theorem alphaWitness_body_shape
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 3) :
    (∃ a b, p = .app .pair (pairArgs a b) ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ a b, p = .imp a b ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ z w a, p = .ex z (.ex w a) ∧
      ((∃ v, a = .var v) ∨ a = .bot)) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      cases sigma
      have hsum : (args 0).complexity + (args 1).complexity = 2 := by
        rw [Pattern.complexity, Fin.sum_univ_two] at h
        omega
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      have hp1 : (args 0).complexity = 1 := by omega
      have hq1 : (args 1).complexity = 1 := by omega
      refine Or.inl ⟨args 0, args 1, ?_,
        alphaWitness_complexity_one _ hp1,
        alphaWitness_complexity_one _ hq1⟩
      congr
      funext i
      fin_cases i <;> rfl
  | imp a b =>
      have hsum : a.complexity + b.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      have ha := alphaWitness_complexity_pos a
      have hb := alphaWitness_complexity_pos b
      have ha1 : a.complexity = 1 := by omega
      have hb1 : b.complexity = 1 := by omega
      exact Or.inr (Or.inl ⟨a, b, rfl,
        alphaWitness_complexity_one _ ha1,
        alphaWitness_complexity_one _ hb1⟩)
  | ex z q =>
      have hq : q.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      obtain ⟨w, a, rfl, ha⟩ := alphaWitness_complexity_two q hq
      exact Or.inr (Or.inr ⟨z, w, a, rfl, ha⟩)
private theorem alphaBlocked_alphaEq_app_no_bot {x' : Nat}
    {a b : Pattern AlphaWitnessSig Nat}
    (halpha : Pattern.AlphaEq alphaBlocked
      (.ex x' (.app .pair (pairArgs a b)))) : a ≠ .bot ∧ b ≠ .bot := by
  constructor
  · intro ha
    subst a
    have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden
  · intro hb
    subst b
    have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden
private theorem alphaBlocked_alphaEq_app_variables {x' a b : Nat}
    (halpha : Pattern.AlphaEq alphaBlocked
      (.ex x' (.app .pair (pairArgs (.var a) (.var b))))) :
    a = x' ∧ b = 0 := by
  have hax : a = x' := by
    by_contra hax
    have hden := halpha.denote_eq
      (M := alphaFirstSelectorModel) (rho := fun _ => false)
    have hleft : true ∈ alphaFirstSelectorModel.denote
        (fun _ => false) alphaBlocked := by
      simp only [alphaFirstSelectorModel, Fin.isValue, alphaBlocked,
        denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
        denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
        zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq,
        and_true, Bool.exists_bool, and_self]
      exact Or.inr ⟨boolPair true false, by simp [boolPair]⟩
    rw [hden] at hleft
    simp [alphaFirstSelectorModel, Model.app, pairArgs, hax] at hleft
    aesop
  refine ⟨hax, ?_⟩
  subst a
  by_contra hb0
  have hden := halpha.denote_eq
    (M := alphaCornerSelectorModel) (rho := fun n => n = 0)
  have hleft : true ∈ alphaCornerSelectorModel.denote
      (fun n => n = 0) alphaBlocked := by
    simp only [alphaCornerSelectorModel, Fin.isValue, alphaBlocked,
      denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
      denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
      zero_ne_one, not_false_eq_true, Function.update_of_ne, decide_true,
      Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq, and_true,
      Bool.exists_bool, and_self]
    exact Or.inl ⟨boolPair false true, by simp [boolPair]⟩
  rw [hden] at hleft
  by_cases hbx : b = x'
  · simp [alphaCornerSelectorModel, Model.app, pairArgs, hbx] at hleft
    aesop
  · simp [alphaCornerSelectorModel, Model.app, pairArgs, hb0, hbx] at hleft
    aesop
private theorem alphaBlocked_not_alphaEq_imp {x' : Nat}
    {a b : Pattern AlphaWitnessSig Nat}
    (ha : (∃ z, a = .var z) ∨ a = .bot)
    (hb : (∃ z, b = .var z) ∨ b = .bot)
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' (.imp a b))) : False := by
  rcases ha with ⟨a, rfl⟩ | rfl <;>
    rcases hb with ⟨b, rfl⟩ | rfl
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      Set.union_singleton] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp only [alphaUnitFullModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, exists_const, Set.ofPred_true,
      denote_imp, denote_bot, Set.union_empty] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      denote_bot, Set.compl_empty, Set.union_singleton, Set.mem_univ,
      Set.insert_eq_of_mem] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      denote_bot, Set.compl_empty, Set.union_empty] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
private theorem alphaBlocked_not_alphaEq_nested_ex {x' z w : Nat}
    {a : Pattern AlphaWitnessSig Nat}
    (ha : (∃ v, a = .var v) ∨ a = .bot)
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' (.ex z (.ex w a)))) : False := by
  rcases ha with ⟨a, rfl⟩ | rfl
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty,
      Set.iUnion_singleton_eq_range, Set.range_id'] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden
private theorem alphaBlocked_alphaEq_body_shape {x' : Nat}
    {p' : Pattern AlphaWitnessSig Nat}
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' p')) :
    ∃ a b, p' = .app .pair (pairArgs (.var a) (.var b)) ∧
      a = x' ∧ b = 0 := by
  have hpComplexity : p'.complexity = 3 := by
    have hc := halpha.complexity_eq
    simp [alphaBlocked, Pattern.complexity, Fin.sum_univ_two, pairArgs] at hc
    omega
  rcases alphaWitness_body_shape p' hpComplexity with
      ⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩ |
        ⟨z, w, a, rfl, ha⟩
  · obtain ⟨hna, hnb⟩ := alphaBlocked_alphaEq_app_no_bot halpha
    rcases ha with ⟨a, rfl⟩ | rfl
    · rcases hb with ⟨b, rfl⟩ | rfl
      · obtain ⟨hax, hb0⟩ := alphaBlocked_alphaEq_app_variables halpha
        exact ⟨a, b, rfl, hax, hb0⟩
      · exact (hnb rfl).elim
    · exact (hna rfl).elim
  · exact (alphaBlocked_not_alphaEq_imp ha hb halpha).elim
  · exact (alphaBlocked_not_alphaEq_nested_ex ha halpha).elim
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
    ¬ AlphaFreshWitnessed alphaWitnessTheory := by
  intro hFresh
  obtain ⟨x', p', y, halpha, hyFresh, hyImp⟩ := hFresh alphaBlocked_mem
  obtain ⟨a, b, hp', hax, hb⟩ := alphaBlocked_alphaEq_body_shape halpha
  subst a
  subst b
  subst p'
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    apply hyFresh
    simp [Pattern.allVars, pairArgs]
  have he' : Pattern.ex x'
      (.app AlphaWitnessSym.pair (pairArgs (.var x') (.var 0))) ∈
        alphaWitnessTheory :=
    (alphaWitnessTheory_isMCS.alphaEq_mem_iff halpha).mp alphaBlocked_mem
  change true ∈ alphaWitnessModel.denote alphaWitnessRho
    (.imp (.ex x' (.app .pair (pairArgs (.var x') (.var 0))))
      (Pattern.captureAvoidingSubst x' y
        (.app .pair (pairArgs (.var x') (.var 0))))) at hyImp
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  rcases hyImp with hnot | hinstance
  · exact hnot he'
  · by_cases hx0 : x' = 0
    · subst x'
      simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0] at hinstance
      aesop
    · simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0,
        Ne.symm hx0] at hinstance
      aesop
end MatchingLogic
