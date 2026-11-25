-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.lintegral_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:05.995799+00:00
-- url     : https://prove2.me/submissions/16aaf58b-38b6-42b0-b8c8-bdc9fac83f91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_continuous_sqLen
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_sqLen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution (n : ℕ) (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Fin n → ℂ, F (s * sqLen w)
      = ENNReal.ofReal (s ^ (-(n : ℝ))) * ∫⁻ w : Fin n → ℂ, F (sqLen w) := by
  have hm : Measurable fun w : Fin n → ℂ => F (sqLen w) := hF.comp (continuous_sqLen n).measurable
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h1 : ∀ w : Fin n → ℂ, s * sqLen w = sqLen (Real.sqrt s • w) := by
    intro w
    simp only [sqLen, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt hs.le]
  simp only [h1]
  rw [← lintegral_map hm (measurable_const_smul (Real.sqrt s)),
    Measure.map_addHaar_smul volume hr, lintegral_smul_measure, smul_eq_mul]
  congr 2
  have hd : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hs.le, Real.rpow_neg hs.le, Real.rpow_natCast,
    abs_of_nonneg (by positivity)]
end GlobalTheory.HCXi.ConeZero
