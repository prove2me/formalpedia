-- Prove2me | solution 1 for MatchingLogic.EntryIII.realize_toFOSentence_ofFOStructure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:29.89792+00:00
-- url     : https://prove2.me/submissions/fbcf3c8b-f181-4471-bb90-a34c8f2bb908

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_realize_toFOAux_of_rel

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution (A : Type) [Nonempty A]
    [(relLanguage S)[[Option Var]].Structure A] (p : Pattern S Var) :
    A ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      Model.ofFOCurrent (S := S) (Var := Var) A ∈
        (Model.ofFOStructure (S := S) (Var := Var) A).denote
          (Model.ofFOValuation (S := S) (Var := Var) A) p := by
  let : (relLanguage S).Structure A :=
    ((relLanguage S).lhomWithConstants (Option Var)).reduct A
  have : ((relLanguage S).lhomWithConstants (Option Var)).IsExpansionOn A :=
    inferInstance
  unfold MatchingLogic.EntryIII.Pattern.toFOSentence
  rw [FirstOrder.Language.Formula.realize_equivSentence]
  unfold MatchingLogic.EntryIII.Pattern.toFOFormula
  rw [realize_toFOAux_of_rel
    (Model.ofFOStructure (S := S) (Var := Var) A)]
  · rfl
  · intro sigma out args
    rfl
end MatchingLogic.EntryIII
