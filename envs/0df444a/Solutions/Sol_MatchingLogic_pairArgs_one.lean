-- Prove2me | solution 1 for MatchingLogic.pairArgs_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:37.79266+00:00
-- url     : https://prove2.me/submissions/e6c48b6b-96fe-4cac-96b8-093a33c7e9b9

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
namespace MatchingLogic
theorem _root_.solution (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 1 = q := rfl
end MatchingLogic
