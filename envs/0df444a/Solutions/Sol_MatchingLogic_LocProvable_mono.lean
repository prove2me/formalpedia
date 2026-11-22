-- Prove2me | solution 1 for MatchingLogic.LocProvable.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:56.340886+00:00
-- url     : https://prove2.me/submissions/1c06b776-327d-4b93-8adf-b090af50b349

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.LocProvable
namespace MatchingLogic.LocProvable
theorem _root_.solution {Gamma Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGD : Gamma ⊆ Delta) (h : LocProvable Gamma phi) : LocProvable Delta phi := by
  rcases h with ⟨l, hl, hp⟩
  exact ⟨l, fun delta hdelta => hGD (hl delta hdelta), hp⟩
end MatchingLogic.LocProvable
