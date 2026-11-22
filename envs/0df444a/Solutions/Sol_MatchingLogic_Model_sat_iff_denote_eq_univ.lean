-- Prove2me | solution 1 for MatchingLogic.Model.sat_iff_denote_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:05.162611+00:00
-- url     : https://prove2.me/submissions/88b585ba-fd6e-41f2-834a-f68f8d68769b

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Theorems.Thm_MatchingLogic_denote_closed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace Model
theorem _root_.solution (M : Model S) {φ : Pattern S Var}
    (hφ : Closed φ) (ρ : Var → M.carrier) :
    M.Sat φ ↔ M.denote ρ φ = Set.univ := by
  constructor
  · intro hsat
    exact hsat ρ
  · intro hden ρ'
    unfold Model.Total
    rw [denote_closed M hφ ρ' ρ]
    exact hden
end Model
end MatchingLogic
