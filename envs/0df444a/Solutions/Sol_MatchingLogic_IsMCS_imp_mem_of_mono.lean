-- Prove2me | solution 1 for MatchingLogic.IsMCS.imp_mem_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:50.273844+00:00
-- url     : https://prove2.me/submissions/56aaa8a9-349b-4854-8515-26a7225931f6

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
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Provable (∅ : Set (Pattern S Nat)) (.imp p' p))
    (hq : Provable (∅ : Set (Pattern S Nat)) (.imp q q'))
    (hmem : Pattern.imp p q ∈ Gamma) : Pattern.imp p' q' ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.imp_mono hp hq)
end MatchingLogic.IsMCS
