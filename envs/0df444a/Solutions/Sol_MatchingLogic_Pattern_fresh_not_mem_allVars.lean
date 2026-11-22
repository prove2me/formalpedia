-- Prove2me | solution 1 for MatchingLogic.Pattern.fresh_not_mem_allVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:45.891074+00:00
-- url     : https://prove2.me/submissions/327a6b13-6052-4577-8d3d-c35f27ccfc57

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution (p : Pattern S Nat) : p.fresh ∉ p.allVars := by
  intro hmem
  have hle := (insert 0 p.allVars).le_max' p.fresh
    (Finset.mem_insert_of_mem hmem)
  unfold fresh at hle
  omega
end MatchingLogic.Pattern
