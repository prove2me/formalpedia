-- Prove2me | solution 1 for MatchingLogic.IsMCS.mem_of_provable_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:59.214945+00:00
-- url     : https://prove2.me/submissions/6cd7827d-6ec8-40d8-bff5-412f610f10e9

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_empty
public import Theorems.Thm_MatchingLogic_IsMCS_mp_mem


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (hp : p ∈ Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q)) : q ∈ Gamma :=
  hM.mp_mem hp (hM.mem_of_provable_empty hpq)
end MatchingLogic.IsMCS
