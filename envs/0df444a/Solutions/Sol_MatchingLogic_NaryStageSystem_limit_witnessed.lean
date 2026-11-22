-- Prove2me | solution 1 for MatchingLogic.NaryStageSystem.limit_witnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:13.954576+00:00
-- url     : https://prove2.me/submissions/72797887-a4ca-4e52-b951-bdf607f733ef

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_FreshWitnessed_toWitnessed


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
theorem _root_.solution (henum : Function.Surjective enum)
    (i : Fin (S.arity sigma)) : Witnessed (T.limit i) :=
  FreshWitnessed.toWitnessed (T.limit_freshWitnessed henum i)
end MatchingLogic.NaryStageSystem
