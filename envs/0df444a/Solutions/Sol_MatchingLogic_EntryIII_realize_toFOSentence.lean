-- Prove2me | solution 1 for MatchingLogic.EntryIII.realize_toFOSentence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:06.649742+00:00
-- url     : https://prove2.me/submissions/6850c7c5-5ba6-4e13-9cf2-3fca773d2279

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_realize_toFOAux

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution (M : Model S) (rho : Var → M.carrier)
    (u : M.carrier) (p : Pattern S Var) :
    letI : (relLanguage S).Structure M.carrier := Model.toFOStructure M
    letI : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
      FirstOrder.Language.constantsOn.structure
        (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
    M.carrier ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      u ∈ M.denote rho p := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  let : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
    FirstOrder.Language.constantsOn.structure
      (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  unfold MatchingLogic.EntryIII.Pattern.toFOSentence
  rw [FirstOrder.Language.Formula.realize_equivSentence]
  unfold MatchingLogic.EntryIII.Pattern.toFOFormula
  have hv :
      (fun a => ((relLanguage S).con a : M.carrier)) =
        MatchingLogic.EntryIII.Model.toFOParameters M rho u := by
    funext a
    cases a <;> rfl
  rw [hv]
  have h := realize_toFOAux M p some none
    (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  have hrho :
      MatchingLogic.EntryIII.Model.toFOParameters M rho u ∘ some = rho := by
    funext x
    rfl
  rwa [hrho] at h
end MatchingLogic.EntryIII
