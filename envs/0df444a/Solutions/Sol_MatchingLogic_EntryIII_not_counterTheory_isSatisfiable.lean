-- Prove2me | solution 1 for MatchingLogic.EntryIII.not_counterTheory_isSatisfiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:07.075554+00:00
-- url     : https://prove2.me/submissions/8e575e13-2ac6-4e4a-9624-e9e6ade1781e

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_realize_toFOSentence_ofFOStructure
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
theorem _root_.solution {Delta : Set (Pattern S Var)}
    {phi : Pattern S Var} (hlocal : LocalCons Delta phi) :
    ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  intro hsat
  let A := hsat.some
  let M : Model S := Model.ofFOStructure (S := S) (Var := Var) A
  let rho : Var → M.carrier := Model.ofFOValuation (S := S) (Var := Var) A
  let u : M.carrier := Model.ofFOCurrent (S := S) (Var := Var) A
  have hDelta : u ∈ M.denoteSet rho Delta := by
    simp only [MatchingLogic.Model.denoteSet, Set.mem_iInter]
    intro delta hdelta
    apply (realize_toFOSentence_ofFOStructure (S := S) (Var := Var) A delta).mp
    exact (counterTheory Delta phi).realize_sentence_of_mem
      (Set.mem_union_left _ ⟨delta, hdelta, rfl⟩)
  have hphi : u ∈ M.denote rho phi := hlocal M rho hDelta
  have hnphi : ¬ u ∈ M.denote rho phi := by
    intro hu
    have hsent :=
      (realize_toFOSentence_ofFOStructure (S := S) (Var := Var) A phi).mpr hu
    have hnSent : A ⊨ (MatchingLogic.EntryIII.Pattern.toFOSentence phi).not :=
      (counterTheory Delta phi).realize_sentence_of_mem
        (Set.mem_union_right _ (Set.mem_singleton _))
    exact ((FirstOrder.Language.Sentence.realize_not A).mp hnSent) hsent
  exact hnphi hphi
end MatchingLogic.EntryIII
