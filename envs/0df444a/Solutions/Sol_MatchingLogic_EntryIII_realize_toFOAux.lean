-- Prove2me | solution 1 for MatchingLogic.EntryIII.realize_toFOAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:26.890634+00:00
-- url     : https://prove2.me/submissions/b12694a3-df15-464a-a322-784e53c7e03a

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
theorem _root_.solution (M : Model S) (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    @FirstOrder.Language.Formula.Realize (relLanguage S) M.carrier
        (Model.toFOStructure M) alpha
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  apply realize_toFOAux_of_rel M
  intro sigma out args
  rfl
end MatchingLogic.EntryIII
