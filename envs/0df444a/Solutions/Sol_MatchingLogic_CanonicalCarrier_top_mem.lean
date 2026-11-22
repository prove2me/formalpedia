-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.top_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:13.417553+00:00
-- url     : https://prove2.me/submissions/c112d505-2b5c-4e3f-9379-2d85304f8062

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_GeneratedCarrier_isMCS
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_empty
public import Theorems.Thm_MatchingLogic_provable_top


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
namespace CanonicalCarrier
theorem _root_.solution (world : CanonicalCarrier S) :
    (Pattern.tp : Pattern S Nat) ∈ (world : Set (Pattern S Nat)) :=
  (CanonicalCarrier.isMCS world).mem_of_provable_empty
    (provable_top (∅ : Set (Pattern S Nat)))
end CanonicalCarrier
end MatchingLogic
