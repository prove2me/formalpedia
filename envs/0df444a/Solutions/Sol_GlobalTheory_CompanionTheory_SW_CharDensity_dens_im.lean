-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.dens_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:06:51.800196+00:00
-- url     : https://prove2.me/submissions/243189a7-71bf-445c-8b63-7f2731434d38

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_tendsto_smoothed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) (y : V) :
    (dens μ y).im = 0 := by
  have t := (Complex.continuous_im.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine tendsto_nhds_unique t ?_
  simp [Function.comp_def]
end GlobalTheory.CompanionTheory.SW.CharDensity
