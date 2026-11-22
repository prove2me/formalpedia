-- Prove2me | solution 1 for MatchingLogic.IsMCS.exists_joint_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:52.032738+00:00
-- url     : https://prove2.me/submissions/8c5bdb33-55c1-446e-b933-a7448d894cdb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Theorems.Thm_MatchingLogic_IsMCS_app_joint_choice

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (L : Fin (S.arity sigma) -> List (Pattern S Nat))
    (psi : Pattern S Nat)
    (happ : Pattern.app sigma (fun i => conj (L i)) ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i => Pattern.and (conj (L i))
        (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by
  exact hM.app_joint_choice (fun i => conj (L i)) psi happ
end IsMCS
end MatchingLogic
