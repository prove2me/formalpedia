-- Prove2me | solution 1 for MatchingLogic.localCons_list_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:27.877841+00:00
-- url     : https://prove2.me/submissions/3a07bca1-b0ee-42c7-b55d-222daf967ec8

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Theorems.Thm_MatchingLogic_Model_denote_conj_eq_denoteSet_list

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (l : List (Pattern S Var)) (phi : Pattern S Var) :
    LocalCons {delta | delta ∈ l} phi ↔
      ∀ (M : Model S) (rho : Var → M.carrier),
        M.denote rho (conj l) ⊆ M.denote rho phi := by
  unfold LocalCons
  constructor
  · intro h M rho
    rw [M.denote_conj_eq_denoteSet_list]
    exact h M rho
  · intro h M rho
    rw [← M.denote_conj_eq_denoteSet_list]
    exact h M rho
end MatchingLogic
