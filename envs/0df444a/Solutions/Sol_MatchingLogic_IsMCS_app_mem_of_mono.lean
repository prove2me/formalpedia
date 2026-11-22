-- Prove2me | solution 1 for MatchingLogic.IsMCS.app_mem_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:18.003772+00:00
-- url     : https://prove2.me/submissions/a8f31dda-c029-4114-98e8-ab2d726ca359

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
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (hargs : ∀ i, Provable (∅ : Set (Pattern S Nat)) (.imp (args i) (args' i)))
    (hmem : Pattern.app sigma args ∈ Gamma) : Pattern.app sigma args' ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.app_mono hargs)
end MatchingLogic.IsMCS
