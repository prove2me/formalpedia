-- Prove2me | solution 1 for MatchingLogic.Model.denote_extendSignature_restrictSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:03.440352+00:00
-- url     : https://prove2.me/submissions/49f13a5f-173c-484d-91fc-e6029c6cf3ed

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Model_denote_extendSignature_liftSignature
public import Theorems.Thm_MatchingLogic_Pattern_lift_restrictSignature
public import Theorems.Thm_MatchingLogic_Provable_liftSignature


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Model
namespace MatchingLogic.Model
theorem _root_.solution [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (p : Pattern S Var) (h : p.symbolSupport ⊆ F) :
    (M.extendSignature F).denote rho p = M.denote rho (p.restrictSignature F h) := by
  have hp : (p.restrictSignature F h).liftSignature F = p :=
    Pattern.lift_restrictSignature F p h
  calc
    (M.extendSignature F).denote rho p =
        (M.extendSignature F).denote rho ((p.restrictSignature F h).liftSignature F) :=
      congrArg ((M.extendSignature F).denote rho) hp.symm
    _ = M.denote rho (p.restrictSignature F h) :=
      M.denote_extendSignature_liftSignature F rho (p.restrictSignature F h)
end MatchingLogic.Model
