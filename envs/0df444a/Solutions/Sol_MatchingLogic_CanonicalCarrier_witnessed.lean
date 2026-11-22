-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.witnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:45.090286+00:00
-- url     : https://prove2.me/submissions/77e9e3c3-adfc-471f-ad6c-7d3ece745790

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_freshWitnessed
public import Theorems.Thm_MatchingLogic_FreshWitnessed_toWitnessed


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
    Witnessed Gamma.val :=
  FreshWitnessed.toWitnessed (freshWitnessed Gamma)
end MatchingLogic.CanonicalCarrier
