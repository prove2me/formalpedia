-- Prove2me | solution 1 for MatchingLogic.EntryIII.localCons_iff_not_counterTheory_isSatisfiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:39.31689+00:00
-- url     : https://prove2.me/submissions/b1e3eb60-8f45-4b89-8701-446f43421ced

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_not_counterTheory_isSatisfiable
public import Theorems.Thm_MatchingLogic_EntryIII_counterTheory_isSatisfiable_of_counterexample

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.EntryIII
theorem _root_.solution
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  refine ⟨not_counterTheory_isSatisfiable, ?_⟩
  intro hunsat M rho u hu
  by_contra hphi
  exact hunsat (counterTheory_isSatisfiable_of_counterexample M rho u hu hphi)
end MatchingLogic.EntryIII
