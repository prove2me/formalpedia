-- Prove2me | solution 1 for MatchingLogic.IsMCS.alphaEq_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:09.456304+00:00
-- url     : https://prove2.me/submissions/49f38012-e2b3-4d3c-abad-6966374ff99b

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (halpha : Pattern.AlphaEq p q) : p ∈ Gamma ↔ q ∈ Gamma := by
  constructor
  · intro hp
    exact hM.mem_of_provable_imp hp (halpha.forward ∅)
  · intro hq
    exact hM.mem_of_provable_imp hq (halpha.backward ∅)
end MatchingLogic.IsMCS
