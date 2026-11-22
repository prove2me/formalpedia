-- Prove2me | solution 1 for MatchingLogic.Pattern.AlphaEq.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:01.22857+00:00
-- url     : https://prove2.me/submissions/47b102ac-171f-40b6-a1f5-a5883054dc3a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
open MatchingLogic.Pattern.AlphaEq
namespace MatchingLogic.Pattern.AlphaEq
theorem _root_.solution {p q : Pattern S Nat} (h : AlphaEq p q) : AlphaEq q p :=
  ⟨h.backward, h.forward, h.complexity_eq.symm⟩
end MatchingLogic.Pattern.AlphaEq
