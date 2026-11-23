-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.phi_eq_charFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:47.648104+00:00
-- url     : https://prove2.me/submissions/229a6cb3-10f2-406e-a372-afe56be9aafb

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent

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
theorem _root_.solution (μ : Measure V) (x : V) :
    phi μ x = charFun μ ((2 * Real.pi) • x) := by
  unfold phi
  rw [charFun_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [inner_smul_right]
  congr 1
  push_cast
  ring
end GlobalTheory.CompanionTheory.SW.CharDensity
