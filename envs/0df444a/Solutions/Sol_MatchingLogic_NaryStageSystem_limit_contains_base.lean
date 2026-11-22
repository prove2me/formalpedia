-- Prove2me | solution 1 for MatchingLogic.NaryStageSystem.limit_contains_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:47.427541+00:00
-- url     : https://prove2.me/submissions/0f1bef36-4c8b-4816-8162-ad110fede7f3

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.NaryStageSystem
variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)
namespace MatchingLogic.NaryStageSystem
theorem _root_.solution (i : Fin (S.arity sigma)) : phi i ∈ T.limit i :=
  ⟨0, T.base i⟩
end MatchingLogic.NaryStageSystem
