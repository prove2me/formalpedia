-- Prove2me | solution 1 for MatchingLogic.global_completeness_of_localCompleteness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:22.748812+00:00
-- url     : https://prove2.me/submissions/46f3e8d6-a977-40c0-bf8c-2aa64135b1a9

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Completeness
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Tactic.Finiteness.Attr
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Theorems.Thm_MatchingLogic_global_completeness
public import Theorems.Thm_MatchingLogic_soundness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ Provable Γ φ :=
  global_completeness hL soundness hΓ hφ
end MatchingLogic
