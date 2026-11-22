-- Prove2me | solution 1 for MatchingLogic.IsMCS.mem_of_provable_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:46.788215+00:00
-- url     : https://prove2.me/submissions/6a1ed89f-c46e-4b97-a7bd-7a7fe8945ee4

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_IsMCS_mem_iff_locProvable
public import Theorems.Thm_MatchingLogic_LocProvable_of_provable


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {p : Pattern S Nat}
    (hM : IsMCS Gamma) (h : Provable (∅ : Set (Pattern S Nat)) p) : p ∈ Gamma :=
  hM.mem_iff_locProvable.mpr (LocProvable.of_provable h)
end MatchingLogic.IsMCS
