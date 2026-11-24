-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.gauss_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:06.230108+00:00
-- url     : https://prove2.me/submissions/e1226ee6-3cb2-40ab-b632-0ef3c8f5aece

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
theorem _root_.solution {b : ℝ} (hb : 0 < b) (u : V) :
    ∫ x : V, Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ u x : ℝ) : ℂ)) = (ker b u : ℂ) := by
  have hp := Real.pi_pos
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
  unfold ker
  push_cast
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 2
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  rw [hI]
  ring
end GlobalTheory.CompanionTheory.SW.CharDensity
