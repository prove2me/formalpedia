-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.dens_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:06:53.460248+00:00
-- url     : https://prove2.me/submissions/3b06c885-2049-4cad-9867-a34647512cea

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_ker_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_bn_pos
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
    0 ≤ (dens μ y).re := by
  have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine ge_of_tendsto' t fun n => ?_
  simp only [Function.comp_apply, Complex.ofReal_re]
  exact integral_nonneg fun z => ker_nonneg (bn_pos n) _
end GlobalTheory.CompanionTheory.SW.CharDensity
