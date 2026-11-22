-- Prove2me | solution 1 for MatchingLogic.localCons_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:52.509533+00:00
-- url     : https://prove2.me/submissions/c623274b-2f90-458b-957d-de32c329437d

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_localCons_renameInjective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔ LocalCons (Pattern.rename e '' Delta) (phi.rename e) :=
  localCons_renameInjective e e.injective
end MatchingLogic
