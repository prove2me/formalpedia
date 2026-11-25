-- Prove2me | solution 1 for GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:12.935831+00:00
-- url     : https://prove2.me/submissions/24c15fc9-5509-4009-8232-89b09f2840c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
import Theorems.Thm_GlobalTheory_GramCount_prim_of_indep_of_isPrimitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  first | exact @GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | exact GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | (intros; apply GlobalTheory.GramCount.prim_of_indep_of_isPrimitive <;> assumption)
end _root_.GlobalTheory.T
