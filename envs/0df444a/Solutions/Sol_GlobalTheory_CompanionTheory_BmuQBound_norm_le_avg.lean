-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuQBound.norm_le_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:30.346581+00:00
-- url     : https://prove2.me/submissions/ee215b6e-27d8-496f-893b-d6164a859b33

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuotientBoundOfFactorReduceChart
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuQBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuQBound
theorem _root_.solution {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : ∀ t, 0 ≤ φ t)
    (h1 : ∫ t, φ t = 1) (f : (Fin d → ℝ) → V) (hf : Continuous f) (b : V)
    (hb : ∀ t, φ t ≠ 0 → ‖f t - b‖ ≤ ‖b‖ / 2) : ‖b‖ ≤ 2 * ‖∫ t, (φ t : ℂ) • f t‖ := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hcC : HasCompactSupport (fun t => (φ t : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hφf : Integrable (fun t => (φ t : ℂ) • f t) :=
    ((Complex.continuous_ofReal.comp hφ).smul hf).integrable_of_hasCompactSupport hcC.smul_right
  have h2 : Integrable (fun t => (φ t : ℂ) • b) := hφi.ofReal.smul_const b
  have hbi : ∫ t, (φ t : ℂ) • b = b := by
    rw [integral_smul_const, integral_complex_ofReal, h1, Complex.ofReal_one, one_smul]
  have key : ∫ t, (φ t : ℂ) • f t = b + ∫ t, (φ t : ℂ) • (f t - b) := by
    simp_rw [smul_sub]
    rw [integral_sub hφf h2, hbi]
    abel
  have hbound : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ‖b‖ / 2 := by
    have hle : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ∫ t, φ t * (‖b‖ / 2) :=
      norm_integral_le_of_norm_le (hφi.mul_const (‖b‖ / 2)) (ae_of_all _ fun t => ?_)
    · rwa [integral_mul_const, h1, one_mul] at hle
    · by_cases ht : φ t = 0
      · simp [ht]
      · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h0 t)]
        exact mul_le_mul_of_nonneg_left (hb t ht) (h0 t)
  rw [key]
  have h3 : ‖b‖ ≤ ‖b + ∫ t, (φ t : ℂ) • (f t - b)‖ + ‖∫ t, (φ t : ℂ) • (f t - b)‖ := by
    simpa using norm_sub_le (b + ∫ t, (φ t : ℂ) • (f t - b)) (∫ t, (φ t : ℂ) • (f t - b))
  linarith
end GlobalTheory.CompanionTheory.BmuQBound
