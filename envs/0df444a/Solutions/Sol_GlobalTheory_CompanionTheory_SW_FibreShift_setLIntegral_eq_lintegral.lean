-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreShift.setLIntegral_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:25.494927+00:00
-- url     : https://prove2.me/submissions/141d4cdc-5f0e-44ae-a3eb-f9f514f9298f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreShift
namespace GlobalTheory.CompanionTheory.SW.FibreShift
theorem _root_.solution {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by
  rw [← lintegral_indicator hW]
  congr 1
  funext v
  by_cases hv : v ∈ W
  · rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, ha v hv]
end GlobalTheory.CompanionTheory.SW.FibreShift
