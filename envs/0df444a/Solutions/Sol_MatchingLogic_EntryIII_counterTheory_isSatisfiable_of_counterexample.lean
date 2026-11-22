-- Prove2me | solution 1 for MatchingLogic.EntryIII.counterTheory_isSatisfiable_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:52.137565+00:00
-- url     : https://prove2.me/submissions/c7fb6976-4f20-440a-bf68-eb43bf56158e

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_realize_toFOSentence
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (M : Model S) (rho : Var → M.carrier) (u : M.carrier)
    (hDelta : u ∈ M.denoteSet rho Delta) (hphi : u ∉ M.denote rho phi) :
    FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  let : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
    FirstOrder.Language.constantsOn.structure
      (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  have hmodel : M.carrier ⊨ counterTheory Delta phi := by
    rw [FirstOrder.Language.Theory.model_iff]
    intro theta htheta
    rcases htheta with htheta | htheta
    · rcases htheta with ⟨delta, hdelta, rfl⟩
      apply (realize_toFOSentence M rho u delta).mpr
      have hDelta' := hDelta
      simp only [MatchingLogic.Model.denoteSet, Set.mem_iInter] at hDelta'
      exact hDelta' delta hdelta
    · rw [Set.mem_singleton_iff] at htheta
      subst theta
      rw [FirstOrder.Language.Sentence.realize_not]
      intro hsent
      exact hphi ((realize_toFOSentence M rho u phi).mp hsent)
  let : M.carrier ⊨ counterTheory Delta phi := hmodel
  exact FirstOrder.Language.Theory.Model.isSatisfiable M.carrier
end MatchingLogic.EntryIII
