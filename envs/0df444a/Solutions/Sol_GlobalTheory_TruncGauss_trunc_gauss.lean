-- Prove2me | solution 1 for GlobalTheory.TruncGauss.trunc_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:12.097242+00:00
-- url     : https://prove2.me/submissions/1c0b6f93-3341-4ad8-b38a-611c491891e7

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_exists_det_bound
import Theorems.Thm_GlobalTheory_TruncGauss_exists_det_shift
import Theorems.Thm_GlobalTheory_TruncGauss_trunc_lower

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
theorem _root_.solution : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) →
      1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  intro n C ε hε
  set P : ℝ := Real.pi ^ n with hPdef
  have hP : 0 < P := pow_pos Real.pi_pos n
  set r : ℝ := ε * P / 2 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_det_bound n C
  obtain ⟨η, hη, hηd⟩ := exists_det_shift n C r hr
  refine ⟨η, hη, fun δ hδ => ?_⟩
  set A : ℝ := K / P + ε with hAdef
  have hA : 0 < A := by positivity
  set K2 : ℝ := K + r with hK2def
  have hK2 : 0 < K2 := by positivity
  have hs : 0 < r / K2 / A := by positivity
  have hT : Tendsto (fun m : ℕ => Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) * (η * δ ^ 2 / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const ((2 * Real.pi / η) ^ n)
    rw [zero_mul] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  filter_upwards [hT.eventually (gt_mem_nhds hs), eventually_ge_atTop 1] with m hm hm1
  intro H hH hC
  have hl := trunc_lower H hH η δ hη hδ m hm1
  show 1 ≤ _ * _ * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set I := ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set T := Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n with hTdef
  have hT0 : 0 ≤ T := by positivity
  set d := H.det.re with hddef
  set D := (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re with hDdef
  have hd0 : 0 ≤ d := by
    have := (Complex.le_def.mp hH.det_nonneg).1
    simpa using this
  have hdK : d ≤ K := (Complex.re_le_norm _).trans (hK H hC)
  have hDd : D - d < r := by
    have := (Complex.re_le_norm _).trans_lt (hηd H hC)
    rw [Complex.sub_re] at this; exact this
  have hDpos : 0 < D := by
    have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (a := η) hη
    exact (Complex.lt_def.mp (Matrix.PosDef.posSemidef_add hH hηpd).det_pos).1
  have e1 : (d / P + ε) * (P / D) = (d + ε * P) / D := by field_simp
  have e2 : r / K2 ≤ r / D := div_le_div_of_nonneg_left hr.le hDpos (by linarith)
  have e3 : 1 + r / D ≤ (d + ε * P) / D := by
    rw [le_div_iff₀ hDpos, add_mul, div_mul_cancel₀ _ hDpos.ne']
    linarith
  have e4 : (d / P + ε) * T ≤ A * T :=
    mul_le_mul_of_nonneg_right (by have := div_le_div_of_nonneg_right hdK hP.le; linarith) hT0
  have e5 : A * T < r / K2 := by
    have := (lt_div_iff₀ hA).mp hm
    linarith
  have e6 : (d / P + ε) * (P / D - T) ≤ (d / P + ε) * ((m : ℝ) ^ n * I) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  rw [mul_assoc]
  rw [mul_sub, e1] at e6
  linarith
end GlobalTheory.TruncGauss
