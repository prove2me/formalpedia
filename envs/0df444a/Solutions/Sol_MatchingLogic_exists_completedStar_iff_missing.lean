-- Prove2me | solution 1 for MatchingLogic.exists_completedStar_iff_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:02.750569+00:00
-- url     : https://prove2.me/submissions/cd6b617b-77d0-47b4-bbc9-b6adc7304d10

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion
namespace MatchingLogic
theorem _root_.solution (root : CanonicalCarrier S) :
    (∃ point : CompletedCarrier root, point.isStar) ↔ Missing root := by
  constructor
  · rintro ⟨point, hstar⟩
    exact point.property hstar
  · intro hmissing
    exact ⟨completedStar hmissing, rfl⟩
end MatchingLogic
