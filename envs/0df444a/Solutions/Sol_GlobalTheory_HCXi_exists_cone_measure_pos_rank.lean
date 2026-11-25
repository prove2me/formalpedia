-- Prove2me | solution 1 for GlobalTheory.HCXi.exists_cone_measure_pos_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:28.126945+00:00
-- url     : https://prove2.me/submissions/8a085a54-1fd5-4cef-b69a-bc98b26901a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_sfinite
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_sqLen_cont
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_sqLen_nonneg
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_homog
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_ae
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_ne_zero
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_ball_compact
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_gauss_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_mulVec_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_isotropic_cone_finite_measure
import Theorems.Thm_Formalism_FourierDecayAlt_P_isotropic_cone_invariance


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
open GlobalTheory GlobalTheory.HCXi
open ConeOne Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi
theorem _root_.solution : ∀ k r' : ℕ, ∃ m : Measure (Fin (2 * (1 + r') + k + 1) → ℂ), SFinite m ∧ (∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0) ∧ (∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f → (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂m) ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0 ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞ ∧ ∀ g ∈ GV k (1 + r'), (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) = ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m := by
  intro k r'
  have hG : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v)) :=
    (Real.measurable_exp.comp sqLen_cont.measurable.neg).ennreal_ofReal
  refine ⟨coneMeas k r', cone_sfinite k r', cone_ae k r', cone_homog k r', ?_, ?_, ?_⟩
  · intro h
    rw [lintegral_eq_zero_iff hG] at h
    apply cone_ne_zero k r'
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with v hv
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hv
    exact absurd hv (not_le.2 (Real.exp_pos _))
  · exact gauss_finite _ _ sqLen_cont.measurable sqLen_nonneg _ (cone_homog k r')
      (isotropic_cone_finite_measure k r' _ ball_compact)
  · intro g hg
    have h1 := lintegral_map (μ := coneMeas k r') hG (cf_mulVec_meas g)
    rw [isotropic_cone_invariance k r' g hg] at h1
    exact h1.symm
end GlobalTheory.HCXi
