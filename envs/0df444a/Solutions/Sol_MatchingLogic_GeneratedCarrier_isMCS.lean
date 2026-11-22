-- Prove2me | solution 1 for MatchingLogic.GeneratedCarrier.isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:48.875335+00:00
-- url     : https://prove2.me/submissions/2f2dc384-ce95-4379-a9d1-562536590d4a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS


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
    IsMCS world.val.val :=
  CanonicalCarrier.isMCS world.val
end MatchingLogic.GeneratedCarrier
