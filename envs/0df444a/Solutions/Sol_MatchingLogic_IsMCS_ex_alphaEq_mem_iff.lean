-- Prove2me | solution 1 for MatchingLogic.IsMCS.ex_alphaEq_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:55.474823+00:00
-- url     : https://prove2.me/submissions/40377e9d-8ac1-4f5f-a914-3dab9878d9c4

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
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma) (h : Pattern.AlphaEq p q) :
    Pattern.ex x p ∈ Gamma ↔ Pattern.ex x q ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.ex x h)
end MatchingLogic.IsMCS
