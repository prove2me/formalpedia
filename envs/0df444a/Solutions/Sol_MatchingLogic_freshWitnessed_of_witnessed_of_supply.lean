-- Prove2me | solution 1 for MatchingLogic.freshWitnessed_of_witnessed_of_supply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:41.46281+00:00
-- url     : https://prove2.me/submissions/3e5d136e-01c3-44bc-9081-9b5701179716

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessSupply

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution
    {Gamma : Set (Pattern S Nat)} (hSupply : InfiniteWitnessSupply Gamma) :
    FreshWitnessed Gamma := by
  intro x p hex
  obtain ⟨y, hySupply, hyFresh⟩ :=
    (hSupply hex).exists_notMem_finset p.allVars
  exact ⟨y, hyFresh, hySupply⟩
end MatchingLogic
