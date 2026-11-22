-- Prove2me | solution 1 for MatchingLogic.GeneratedCarrier.witnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:50.180798+00:00
-- url     : https://prove2.me/submissions/f80a9ab6-4e50-4126-84d4-8208cb21c548

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_witnessed


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
open MatchingLogic.GeneratedCarrier
namespace MatchingLogic.GeneratedCarrier
theorem _root_.solution {root : CanonicalCarrier S} (world : GeneratedCarrier root) :
    Witnessed world.val.val :=
  CanonicalCarrier.witnessed world.val
end MatchingLogic.GeneratedCarrier
