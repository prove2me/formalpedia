-- Prove2me | solution 1 for MatchingLogic.Pattern.complexity_captureAvoidingSubst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:28.088806+00:00
-- url     : https://prove2.me/submissions/520bc8f5-ae02-4da9-a36c-57b835b87a1a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Pattern_complexity_substVar
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
namespace MatchingLogic.Pattern
theorem _root_.solution (x y : Nat) (p : Pattern S Nat) :
    (captureAvoidingSubst x y p).complexity = p.complexity := by
  rw [captureAvoidingSubst, complexity_substVar]
  exact (avoidBinder_alphaEq y p).complexity_eq.symm
end MatchingLogic.Pattern
