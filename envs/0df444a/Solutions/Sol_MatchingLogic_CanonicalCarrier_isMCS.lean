-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:00.440173+00:00
-- url     : https://prove2.me/submissions/6b694152-5c43-4519-92ba-e1da3e5879ef

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
    IsMCS Gamma.val :=
  Gamma.property.1
end MatchingLogic.CanonicalCarrier
