-- Prove2me | solution 1 for MatchingLogic.IsMCS.bot_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:12.477701+00:00
-- url     : https://prove2.me/submissions/465506e2-e332-4e83-92ee-aae6b4b59dd4

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma) :
    (.bot : Pattern S Nat) ∉ Gamma := by
  intro hbot
  exact hM.1 (LocProvable.of_mem hbot)
end MatchingLogic.IsMCS
