-- Prove2me | solution 1 for MatchingLogic.SetVariables.not_ssat_svar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:39.774778+00:00
-- url     : https://prove2.me/submissions/004788b4-344d-427e-98ae-422a741f609c

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_SetVariables

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.SetVariables
variable {S : Signature} {Var SVar : Type} [DecidableEq Var]
namespace MatchingLogic.SetVariables
theorem _root_.solution (M : Model S) (X : SVar) :
    ¬ SSat (Var := Var) M (.svar X) := by
  intro h
  let a : M.carrier := Classical.choice M.nonempty
  let ρ : SVal M Var SVar := ⟨fun _ => a, fun _ => ∅⟩
  have hρ := h ρ
  change (∅ : Set M.carrier) = Set.univ at hρ
  exact Set.empty_ne_univ hρ
end MatchingLogic.SetVariables
