-- Prove2me | solution 1 for GlobalTheory.T.cyclotomicTower_trace_almost_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:11.252808+00:00
-- url     : https://prove2.me/submissions/ce923017-ae9c-4445-b854-84a6d986cc6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjective
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Theorems.Thm_GlobalTheory_Cyc_trace_almost_onto


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), Kinf K ≤ L → (∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) → (∀ s ∈ S, s ∈ Hinf K) → (∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) → ∀ a : Om l, a ∈ Kinf K → ‖a‖ < 1 → ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  first | exact @GlobalTheory.Cyc.trace_almost_onto | exact GlobalTheory.Cyc.trace_almost_onto | (intros; apply GlobalTheory.Cyc.trace_almost_onto <;> assumption)
end _root_.GlobalTheory.T
