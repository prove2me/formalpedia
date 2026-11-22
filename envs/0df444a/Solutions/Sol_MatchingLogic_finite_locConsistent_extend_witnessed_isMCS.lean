-- Prove2me | solution 1 for MatchingLogic.finite_locConsistent_extend_witnessed_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:42.435321+00:00
-- url     : https://prove2.me/submissions/997ffdfd-9e34-4a54-aa46-a55dcc087224

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_FreshWitnessed_toWitnessed
public import Theorems.Thm_MatchingLogic_finite_locConsistent_extend_freshWitnessed_isMCS

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
    [Countable (Pattern S Nat)] (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by
  obtain ⟨Delta, hbaseDelta, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS base hbase
  exact ⟨Delta, hbaseDelta, hM, hW.toWitnessed⟩
end MatchingLogic
