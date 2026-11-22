-- Prove2me | solution 1 for MatchingLogic.Model.denote_extendSignature_liftSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:11.812939+00:00
-- url     : https://prove2.me/submissions/f4f50f86-26ce-426c-ad72-c544c75aaf2e

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Model_app_extendSignature
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
    (p : Pattern (S.restrict F) Var) :
    (M.extendSignature F).denote rho (p.liftSignature F) = M.denote rho p := by
  induction p generalizing rho with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      change (M.extendSignature F).app sigma.1
          (fun i => (M.extendSignature F).denote rho ((args i).liftSignature F)) =
        M.app sigma (fun i => M.denote rho (args i))
      rw [M.app_extendSignature F sigma]
      congr 1
      funext i
      exact ih i rho
  | imp phi psi ihphi ihpsi =>
      change ((M.extendSignature F).denote rho (phi.liftSignature F))ᶜ ∪
          (M.extendSignature F).denote rho (psi.liftSignature F) =
        (M.denote rho phi)ᶜ ∪ M.denote rho psi
      rw [ihphi rho, ihpsi rho]
  | ex x phi ih =>
      change (⋃ a : M.carrier,
        (M.extendSignature F).denote (Function.update rho x a) (phi.liftSignature F)) =
          ⋃ a : M.carrier, M.denote (Function.update rho x a) phi
      apply Set.iUnion_congr
      intro a
      exact ih (Function.update rho x a)
end MatchingLogic.Model
