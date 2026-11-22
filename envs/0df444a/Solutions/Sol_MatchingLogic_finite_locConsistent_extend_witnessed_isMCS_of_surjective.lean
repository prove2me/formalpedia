-- Prove2me | solution 1 for MatchingLogic.finite_locConsistent_extend_witnessed_isMCS_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:41.991772+00:00
-- url     : https://prove2.me/submissions/cf872989-c4fa-41cb-9747-801cb7435664

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_FreshWitnessed_toWitnessed
public import Theorems.Thm_MatchingLogic_finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
theorem _root_.solution
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by
  obtain ⟨Delta, hbaseDelta, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
      enum henum base hbase
  exact ⟨Delta, hbaseDelta, hM, hW.toWitnessed⟩
end MatchingLogic
