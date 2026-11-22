-- Prove2me | solution 1 for MatchingLogic.Provable.captureAvoidingExQuant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:15.034551+00:00
-- url     : https://prove2.me/submissions/8dcebf22-fd25-4b47-92f1-b13c49cc29b3

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
public import Theorems.Thm_MatchingLogic_Pattern_AvoidsBinder_captureFree
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq
public import Theorems.Thm_MatchingLogic_Provable_imp_trans


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (x y : Nat) (p : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.captureAvoidingSubst x y p) (.ex x p)) := by
  have hcf := (Pattern.avoidBinder_avoids y p).captureFree (x := x)
  have hraw : Provable Gamma
      (.imp (substVar x y (Pattern.avoidBinder y p))
        (.ex x (Pattern.avoidBinder y p))) := .exQuant hcf
  have halpha := Pattern.AlphaEq.ex x (Pattern.avoidBinder_alphaEq y p)
  exact hraw.imp_trans (halpha.backward Gamma)
end Provable
end MatchingLogic
