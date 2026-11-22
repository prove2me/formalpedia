-- Prove2me | solution 1 for MatchingLogic.denote_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:31.247311+00:00
-- url     : https://prove2.me/submissions/8f3e7b95-8128-4204-9c7e-6c48909a9014

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Theorems.Thm_MatchingLogic_denote_congr

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) {φ : Pattern S Var} (hφ : Closed φ)
    (ρ ρ' : Var → M.carrier) : M.denote ρ φ = M.denote ρ' φ := by
  apply denote_congr M φ ρ ρ'
  intro x hx
  unfold Closed at hφ
  rw [hφ] at hx
  exact hx.elim
end MatchingLogic
