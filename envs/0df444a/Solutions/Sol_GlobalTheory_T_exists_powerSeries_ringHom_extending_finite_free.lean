-- Prove2me | solution 1 for GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:06.865569+00:00
-- url     : https://prove2.me/submissions/05a8adc1-6862-45c0-8955-d6e18d644c1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFreeStatement
import Theorems.Thm_GlobalTheory_powerSeries_extend_finite_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) → ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = i PowerSeries.X ∧ ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first | exact @GlobalTheory.powerSeries_extend_finite_free | exact GlobalTheory.powerSeries_extend_finite_free | (intros; apply GlobalTheory.powerSeries_extend_finite_free <;> assumption)
end _root_.GlobalTheory.T
