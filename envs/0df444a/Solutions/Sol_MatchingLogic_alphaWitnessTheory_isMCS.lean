-- Prove2me | solution 1 for MatchingLogic.alphaWitnessTheory_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:39.751455+00:00
-- url     : https://prove2.me/submissions/41c17e2d-3f27-4539-a21f-ce41fb94844b

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
public import Theorems.Thm_MatchingLogic_pointedTheory_isMCS


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
namespace MatchingLogic
theorem _root_.solution : IsMCS alphaWitnessTheory := by
  exact pointedTheory_isMCS alphaWitnessModel alphaWitnessRho true
end MatchingLogic
