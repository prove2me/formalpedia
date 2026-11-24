-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.smoothed_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:10.956857+00:00
-- url     : https://prove2.me/submissions/04d619d0-10b8-4350-9e56-b2880d2e90d1

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_integrable_gauss
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_gauss_inner

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
    ∫ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ((∫ z, ker b (z - y) ∂μ : ℝ) : ℂ) := by
  set F : V → V → ℂ := fun x z => Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ (z - y) x : ℝ) : ℂ)) with hF
  have h1 : ∀ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ∫ z, F x z ∂μ := by
    intro x
    unfold phi
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF, ← Complex.exp_add, inner_sub_left]
    congr 1
    push_cast
    ring
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod μ) := by
    have hg := (integrable_gauss (V := V) hb).comp_fst μ
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, hF, Complex.norm_exp]
      apply le_of_eq
      congr 1
      simp [← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
  simp_rw [h1]
  rw [integral_integral_swap hint, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact gauss_inner hb _
end GlobalTheory.CompanionTheory.SW.CharDensity
