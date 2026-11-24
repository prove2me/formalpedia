-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.lintegral_bump_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:18.925527+00:00
-- url     : https://prove2.me/submissions/2372e8b7-8d00-4168-9fff-2ff5c24f18b7

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
theorem _root_.solution (m : Measure V) {O : Set V} (hO : IsOpen O) {φ : V → ℝ}
    (h1 : ∀ v, φ v ≤ 1) (hs : tsupport φ ⊆ O) : ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ m O := by
  rw [← lintegral_indicator_one hO.measurableSet]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ O
  · simpa [Set.indicator_apply, hv] using h1 v
  · have hz : φ v = 0 := by
      by_contra hne
      exact hv (hs (subset_tsupport φ hne))
    simp [Set.indicator_apply, hv, hz]
end GlobalTheory.CompanionTheory.SW.FibreFam
