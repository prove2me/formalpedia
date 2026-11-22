-- Prove2me | solution 1 for MatchingLogic.IsMCS.ex_mem_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:43.519301+00:00
-- url     : https://prove2.me/submissions/e46882e6-fc92-42f8-8f20-072d2c7c0d16

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
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q))
    (hmem : Pattern.ex x p ∈ Gamma) : Pattern.ex x q ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.ex_mono hpq)
end MatchingLogic.IsMCS
