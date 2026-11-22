-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.freshWitnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:57.175515+00:00
-- url     : https://prove2.me/submissions/d73ff8d9-0bfb-42c9-ad2f-105588a9e226

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore
open MatchingLogic.CanonicalCarrier
namespace MatchingLogic.CanonicalCarrier
theorem _root_.solution (Gamma : CanonicalCarrier S) :
    FreshWitnessed Gamma.val :=
  Gamma.property.2
end MatchingLogic.CanonicalCarrier
