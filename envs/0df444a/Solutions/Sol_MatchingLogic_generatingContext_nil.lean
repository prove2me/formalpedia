-- Prove2me | solution 1 for MatchingLogic.generatingContext_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:41.232822+00:00
-- url     : https://prove2.me/submissions/e4f440fa-4810-4aab-b035-c4b5a37d29c3

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
theorem _root_.solution :
    generatingContext ([] : List (Coord S)) = (.hole : AppCtx S Nat) :=
  rfl
end MatchingLogic
