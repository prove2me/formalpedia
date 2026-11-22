-- Prove2me | solution 1 for MatchingLogic.IsMCS.app_alphaEq_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:59.439212+00:00
-- url     : https://prove2.me/submissions/c6f5569d-9840-428e-80fa-e4dcaa9ab509

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
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (h : ∀ i, Pattern.AlphaEq (args i) (args' i)) :
    Pattern.app sigma args ∈ Gamma ↔ Pattern.app sigma args' ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.app h)
end MatchingLogic.IsMCS
