-- Prove2me | solution 1 for MatchingLogic.henkinLimit_locConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:17.29959+00:00
-- url     : https://prove2.me/submissions/7509b93c-b0bd-46e6-b5cc-06626c373537

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_henkinLimit_covers_list

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
    (stageTheory : List (Pattern S Nat) → Set (Pattern S Nat))
    (step : List (Pattern S Nat) → Pattern S Nat → List (Pattern S Nat))
    (enum : Nat → Pattern S Nat) (base : List (Pattern S Nat))
    (hstep : ∀ stage phi, stageTheory stage ⊆ stageTheory (step stage phi))
    (hconsistent : ∀ n,
      LocConsistent (stageTheory (henkinStages step enum base n))) :
    LocConsistent (henkinLimit stageTheory step enum base) := by
  intro hbad
  rcases hbad with ⟨l, hl, hp⟩
  obtain ⟨n, hn⟩ :=
    henkinLimit_covers_list stageTheory step enum base l hstep hl
  exact hconsistent n ⟨l, hn, hp⟩
end MatchingLogic
