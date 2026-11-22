-- Prove2me | solution 1 for MatchingLogic.Pattern.AlphaEq.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:17.145894+00:00
-- url     : https://prove2.me/submissions/ad43ac30-dbdd-4cb3-9caf-2f550b9fd176

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Provable_imp_trans


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
open MatchingLogic.Pattern.AlphaEq
namespace MatchingLogic.Pattern.AlphaEq
theorem _root_.solution {p q r : Pattern S Nat} (hpq : AlphaEq p q) (hqr : AlphaEq q r) :
    AlphaEq p r :=
  ⟨fun Gamma => (hpq.forward Gamma).imp_trans (hqr.forward Gamma),
   fun Gamma => (hqr.backward Gamma).imp_trans (hpq.backward Gamma),
   hpq.complexity_eq.trans hqr.complexity_eq⟩
end MatchingLogic.Pattern.AlphaEq
