-- Prove2me | solution 1 for GlobalTheory.TruncGauss.trunc_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:54.688133+00:00
-- url     : https://prove2.me/submissions/0cd5a0fd-238e-4219-8087-bbf15d087631

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_qf_re_nonneg
import Theorems.Thm_GlobalTheory_TruncGauss_qf_smul_one_re
import Theorems.Thm_GlobalTheory_TruncGauss_qf_shift_re
import Theorems.Thm_GlobalTheory_T_integral_exp_neg_hermitian_form_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    Real.pi ^ n / (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re
        - Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n ≤
      (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Hη := H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hHη
  have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (a := η) hη
  have hHηpd : Hη.PosDef := Matrix.PosDef.posSemidef_add hH hηpd
  have hMpd : ((m : ℂ) • Hη).PosDef := hHηpd.smul (a := (m : ℝ)) hm0
  set b : ℝ := m * η / 2 with hb
  have hb0 : 0 < b := by positivity
  have hGpd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := Matrix.PosDef.one.smul (a := b) hb0
  obtain ⟨hfi, hfint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hMpd
  obtain ⟨hgi, hgint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hGpd
  set f : V n → ℝ := fun w => Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) with hf
  set g : V n → ℝ := fun w => Real.exp (-(b * ‖w‖ ^ 2)) with hg
  have ef : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((m : ℂ) • Hη) j l * w j *
      (starRingEnd ℂ) (w l)).re)) = f := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_shift_re m η H w)
  have eg : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) j l *
      w j * (starRingEnd ℂ) (w l)).re)) = g := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_smul_one_re b w)
  rw [ef] at hfi hfint
  rw [eg] at hgi hgint
  have hD : ((m : ℂ) • Hη).det.re = (m : ℝ) ^ n * Hη.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin, show ((m : ℂ)) ^ n = (((m : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul]
  have hGd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re = b ^ n := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [hD] at hfint
  rw [hGd] at hgint
  have hDpos : 0 < Hη.det.re := by
    have := hHηpd.det_pos
    exact (Complex.lt_def.mp this).1

  have hsplit := integral_add_compl (s := ball (0 : V n) δ) measurableSet_ball hfi
  have htail : ∫ w in (ball (0 : V n) δ)ᶜ, f w ≤ Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on hfi.integrableOn (hgi.const_mul _).integrableOn
      measurableSet_ball.compl fun w hw => ?_).trans
      (setIntegral_le_integral (hgi.const_mul _) (Eventually.of_forall fun w => by positivity))
    have hw' : δ ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
    have hq := qf_re_nonneg H hH w
    simp only [hf, hg]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ.le hw' 2
    have h2 : 0 ≤ (m : ℝ) * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_nonneg hm0.le hq]
  have hmain : (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w =
      Real.pi ^ n / Hη.det.re - (m : ℝ) ^ n * ∫ w in (ball (0 : V n) δ)ᶜ, f w := by
    rw [eq_sub_iff_add_eq, ← mul_add, hsplit, hfint]
    field_simp
  have hT : (m : ℝ) ^ n * (Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w) =
      Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n := by
    rw [hgint, hb]
    field_simp
    have h1 : η ^ n * η⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη.ne', one_pow]
    have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((m : ℝ) ^ n * Real.pi ^ n * (1 / 2 : ℝ) ^ n * 2 ^ n)) * h1 -
      ((m : ℝ) ^ n * Real.pi ^ n) * h2
  show _ ≤ (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w
  rw [hmain, ← hT]
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg hm0.le n)
  linarith
end GlobalTheory.TruncGauss
