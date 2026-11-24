-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.integrable_ker_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:26.587829+00:00
-- url     : https://prove2.me/submissions/50511419-be75-491b-9465-da274382cb31

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_ker_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_continuous_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_ker_le

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
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    Integrable (fun z => ker b (z - y)) μ := by
  refine Integrable.of_bound (C := (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2)) ?_
    (Eventually.of_forall fun z => ?_)
  · exact ((continuous_ker b).comp (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (ker_nonneg hb _)]
    exact ker_le hb _
end GlobalTheory.CompanionTheory.SW.CharDensity
