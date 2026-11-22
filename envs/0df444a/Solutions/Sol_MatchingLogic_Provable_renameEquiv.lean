-- Prove2me | solution 1 for MatchingLogic.Provable.renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:58.59646+00:00
-- url     : https://prove2.me/submissions/7e7023f9-d5b1-4b71-afd1-04f0c329149a

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Provable_renameInjective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
namespace Provable
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename e '' Gamma) (phi.rename e) :=
  h.renameInjective e e.injective
end Provable
end MatchingLogic
