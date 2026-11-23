-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.continuous_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:09.079719+00:00
-- url     : https://prove2.me/submissions/32fb0052-47cd-4e60-8a4c-72516e614655

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_phi_eq_charFun

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
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] : Continuous (phi μ) := by
  have : phi μ = fun x => charFun μ ((2 * Real.pi) • x) := funext (phi_eq_charFun μ)
  rw [this]
  exact continuous_charFun.comp (continuous_const_smul _)
end GlobalTheory.CompanionTheory.SW.CharDensity
