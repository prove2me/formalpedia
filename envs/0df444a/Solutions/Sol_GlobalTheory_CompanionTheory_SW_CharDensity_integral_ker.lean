-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.integral_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:14.088241+00:00
-- url     : https://prove2.me/submissions/5892109b-7612-4c9d-ac14-794d9bdc7db8

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
theorem _root_.solution {b : ℝ} (hb : 0 < b) : ∫ w : V, ker b w = 1 := by
  have hp := Real.pi_pos
  unfold ker
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  have : Real.pi / b * (Real.pi / (Real.pi ^ 2 / b)) = 1 := by
    field_simp
  rw [this, Real.one_rpow]
end GlobalTheory.CompanionTheory.SW.CharDensity
