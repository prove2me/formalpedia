-- Prove2me | solution 1 for GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:32.846519+00:00
-- url     : https://prove2.me/submissions/e4759a6f-12a0-4ae4-9707-49c417ceb9ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReduction
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReductionStatement
import Theorems.Thm_GlobalTheory_monic_splits_of_separable_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.monic_splits_of_separable_residue | exact GlobalTheory.monic_splits_of_separable_residue | (intros; apply GlobalTheory.monic_splits_of_separable_residue <;> assumption)
end _root_.GlobalTheory.T
