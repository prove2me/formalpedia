-- Prove2me | solution 1 for MatchingLogic.Model.denote_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:53.57207+00:00
-- url     : https://prove2.me/submissions/bdbd6375-5fed-4563-a3c5-e17aef68f94f

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Model_denote_renameInjective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
namespace Model
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename e) = M.denote (rho ∘ e) p :=
  M.denote_renameInjective e e.injective rho p
end Model
end MatchingLogic
