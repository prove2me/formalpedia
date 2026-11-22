-- Prove2me | solution 1 for MatchingLogic.IsMCS.imp_alphaEq_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:53.982575+00:00
-- url     : https://prove2.me/submissions/f76999bb-ff9b-4c67-bf2a-82b221f37f13

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_IsMCS_alphaEq_mem_iff

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Pattern.AlphaEq p p') (hq : Pattern.AlphaEq q q') :
    Pattern.imp p q ∈ Gamma ↔ Pattern.imp p' q' ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.imp hp hq)
end MatchingLogic.IsMCS
