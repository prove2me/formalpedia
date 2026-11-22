-- Prove2me | solution 1 for MatchingLogic.Pattern.IsCaptureAvoidingSubst.complexity_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:28.560189+00:00
-- url     : https://prove2.me/submissions/b90ce066-1da6-4e86-9832-f1050e3dcbac

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

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
namespace MatchingLogic.Pattern
namespace IsCaptureAvoidingSubst
theorem _root_.solution {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) : q.complexity = p.complexity := by
  rcases h with ⟨p', halpha, _hcf, rfl⟩
  rw [complexity_substVar]
  exact halpha.complexity_eq.symm
end IsCaptureAvoidingSubst
end MatchingLogic.Pattern
