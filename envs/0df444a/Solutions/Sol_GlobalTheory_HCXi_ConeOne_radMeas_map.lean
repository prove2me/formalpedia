-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.radMeas_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:49.575205+00:00
-- url     : https://prove2.me/submissions/d99efc71-94a0-4cf4-a40d-2b3b0f667cad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (radMeas N).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ (2 * N + 2))⁻¹) • radMeas N := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hw : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N)) := by fun_prop
  rw [lintegral_map hg hm, lintegral_smul_measure]
  unfold radMeas
  have hgl : Measurable fun a : ℂ => g ((t : ℂ) * a) := hg.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg, lintegral_withDensity_eq_lintegral_mul _ hw hgl]
  have hmap : (volume : Measure ℂ).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ 2)⁻¹) • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure ℂ) ht.ne'
    rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
    exact h
  have h1 := lintegral_map (μ := (volume : Measure ℂ)) (hw.mul hg) hm
  rw [hmap, lintegral_smul_measure] at h1
  have h2 : ∀ c : ℂ, ((fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N))) * fun a => g ((t : ℂ) * a)) c =
      ENNReal.ofReal ((t ^ (2 * N))⁻¹) * (ENNReal.ofReal (‖(t : ℂ) * c‖ ^ (2 * N)) * g ((t : ℂ) * c)) := by
    intro c
    rw [Pi.mul_apply, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [lintegral_congr h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [Pi.mul_apply] at h1 ⊢
  rw [← h1, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add]
end GlobalTheory.HCXi.ConeOne
