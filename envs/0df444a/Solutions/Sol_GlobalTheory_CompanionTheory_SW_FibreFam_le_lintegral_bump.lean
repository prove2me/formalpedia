-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:51.184079+00:00
-- url     : https://prove2.me/submissions/96c2541d-f29c-4745-b954-b3feede7963a

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
theorem _root_.solution [T2Space V] (m : Measure V) {K : Set V} (hK : IsCompact K) {φ : V → ℝ}
    (h0 : ∀ v, 0 ≤ φ v) (h1 : ∀ v ∈ K, φ v = 1) : m K ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [← lintegral_indicator_one hKm]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [Set.indicator_apply, hv, h1 v hv]
  · simp [Set.indicator_apply, hv]
end GlobalTheory.CompanionTheory.SW.FibreFam
