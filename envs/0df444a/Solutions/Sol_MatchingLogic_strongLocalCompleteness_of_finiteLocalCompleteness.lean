-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness_of_finiteLocalCompleteness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:31.687103+00:00
-- url     : https://prove2.me/submissions/d32eb077-b3fd-4f93-aab4-d60ab888ba6e

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Theorems.Thm_MatchingLogic_EntryIII_localCons_compact
public import Theorems.Thm_MatchingLogic_localCons_compact


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (hfinite : FiniteLocalCompleteness S Var) :
    StrongLocalCompleteness S Var := by
  rw [StrongLocalCompleteness]
  intro Delta phi hlocal
  obtain ⟨l, hl, hlocalFinite⟩ := localCons_compact hlocal
  exact ⟨l, hl, hfinite l phi hlocalFinite⟩
end MatchingLogic
