-- Prove2me | solution 1 for MatchingLogic.Pattern.fresh_not_mem_FV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:31.43144+00:00
-- url     : https://prove2.me/submissions/05eec6bf-20fc-48ad-accb-8f0d2960ae63

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
public import Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution (p : Pattern S Nat) : p.fresh ∉ FV p := by
  intro hmem
  exact p.fresh_not_mem_allVars (p.FV_subset_allVars hmem)
end MatchingLogic.Pattern
