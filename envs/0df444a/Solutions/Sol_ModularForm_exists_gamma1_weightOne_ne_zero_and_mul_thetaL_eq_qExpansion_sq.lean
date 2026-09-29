-- Prove2me | solution 1 for ModularForm.exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a139a896-0051-5778-b2a2-ec10695bd075

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularForm_exists_gamma1_isIntegralQExp_eisenstein_four_six
import Theorems.Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open CongruenceSubgroup ModularCurve UpperHalfPlane
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma

noncomputable section

namespace W1OddE96

variable (M : ℕ) [NeZero M]

local notation "Γ₁ℝ" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_gamma1 : (1 : ℝ) ∈ (Γ₁ℝ).strictPeriods := by
  simp

theorem isIntegralQExp_mul {a b : ℤ} (f : ModularForm Γ₁ℝ a) (g : ModularForm Γ₁ℝ b)
    {p q : PowerSeries ℤ} (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g q) :
    IsIntegralQExp (f.mul g) (p * q) := by
  rw [IsIntegralQExp] at hf hg ⊢
  rw [map_mul, hf, hg, ← ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods_gamma1 M) f g]

theorem isIntegralQExp_mcast {a b : ℤ} (h : a = b) (f : ModularForm Γ₁ℝ a) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) : IsIntegralQExp (ModularForm.mcast h f) p := by
  rw [IsIntegralQExp] at hf ⊢
  rw [hf]
  rfl

theorem mk_sigma_three_eq_eisenstein4 :
    (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) = eisenstein4 := by
  ext n
  simp only [eisenstein4, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]

theorem mk_sigma_five_eq_eisenstein6 :
    (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) = eisenstein6 := by
  ext n
  simp only [eisenstein6, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = intSeriesC L q := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, intSeriesC]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]

theorem coeffEmb_thetaL (L : Type*) [Field L] [CharZero L] (f : LaurentSeries ℚ) :
    coeffEmb L (thetaL ℚ f) = thetaL L (coeffEmb L f) := by
  ext n
  rw [coeffEmb_coeff, thetaL_apply, thetaL_apply, ModularCurve.theta_coeff, ModularCurve.theta_coeff,
    coeffEmb_coeff, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]

theorem intSeriesC_ne_zero_of_constantCoeff (K : Type*) [Field K] (q : PowerSeries ℤ)
    (hq : PowerSeries.constantCoeff q = 1) : intSeriesC K q ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at this
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, hq, map_one] at this
  exact one_ne_zero this

end W1OddE96

end

open W1OddE96 in
theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) :
    ∃ (w : ModularForm (Gamma1 M) 1) (v : LaurentSeries ℂ), w ≠ 0 ∧
      v ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) ∧
      v * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ 2 := by
  classical
  obtain ⟨wI⟩ := ModularCurve.nonempty_integralWeightOneForm ℚ M (by omega)
  obtain ⟨E4, E6, hE4, hE6⟩ := ModularForm.exists_gamma1_isIntegralQExp_eisenstein_four_six M
  rw [mk_sigma_three_eq_eisenstein4] at hE4
  rw [mk_sigma_five_eq_eisenstein6] at hE6

  set w := wI.form with hwdef
  set W : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 w) with hWdef
  have hWint : W = intSeriesC ℂ wI.series := by
    rw [hWdef, intSeriesC, ← wI.isIntegralQExp]
  have hWne : intSeriesC ℂ wI.series ≠ 0 := by
    intro h
    apply wI.intSeriesC_ne_zero
    have h' : intSeriesC ℂ wI.series = coeffEmb ℂ (intSeriesC ℚ wI.series) := (coeffEmb_intSeriesC ℂ _).symm
    rw [h'] at h
    exact (map_eq_zero (coeffEmb ℂ)).mp h
  have hw0 : w ≠ 0 := by
    intro h0
    apply hWne
    rw [← hWint, hWdef, h0]
    simp [qExpansion_zero]

  let Nf : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 10 :=
    ModularForm.mcast (by norm_num) ((w.mul w).mul (E4.mul E4))
  let Df : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 10 :=
    ModularForm.mcast (by norm_num) (E4.mul E6)
  have hNf : IsIntegralQExp Nf (wI.series * wI.series * (eisenstein4 * eisenstein4)) :=
    isIntegralQExp_mcast M _ _ (isIntegralQExp_mul M _ _ (isIntegralQExp_mul M _ _ wI.isIntegralQExp wI.isIntegralQExp)
      (isIntegralQExp_mul M _ _ hE4 hE4))
  have hDf : IsIntegralQExp Df (eisenstein4 * eisenstein6) :=
    isIntegralQExp_mcast M _ _ (isIntegralQExp_mul M _ _ hE4 hE6)
  have hE4ne : ∀ (K : Type) [Field K], intSeriesC K eisenstein4 ≠ 0 := fun K _ =>
    intSeriesC_ne_zero_of_constantCoeff K _ constantCoeff_eisenstein4
  have hE6c : PowerSeries.constantCoeff eisenstein6 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [eisenstein6]
  have hE6ne : ∀ (K : Type) [Field K], intSeriesC K eisenstein6 ≠ 0 := fun K _ =>
    intSeriesC_ne_zero_of_constantCoeff K _ hE6c
  have hDne : intSeriesC ℚ (eisenstein4 * eisenstein6) ≠ 0 := by
    rw [intSeriesC_mul]; exact mul_ne_zero (hE4ne ℚ) (hE6ne ℚ)

  have humem : intSeriesC ℂ (wI.series * wI.series * (eisenstein4 * eisenstein4)) /
      intSeriesC ℂ (eisenstein4 * eisenstein6) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) := by
    rw [← coeffEmb_intSeriesC ℂ, ← coeffEmb_intSeriesC ℂ, ← map_div₀]
    exact coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC Nf Df hNf hDf hDne)
  have hjmem : ModularCurve.jqModC ℂ ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) := by
    rw [← map_jqModC (algebraMap ℚ ℂ), jqModC_rat]
    exact coeffEmb_mem_laurentBaseChange ℂ
      (intFormRatiosC_subset ℚ _ (by rw [← jqModC_rat]; exact jqModC_mem_intFormRatiosC ℚ _))

  refine ⟨w, -(intSeriesC ℂ (wI.series * wI.series * (eisenstein4 * eisenstein4)) /
      intSeriesC ℂ (eisenstein4 * eisenstein6) * (ModularCurve.jqModC ℂ)⁻¹), hw0, ?_, ?_⟩
  · exact neg_mem (mul_mem humem (inv_mem hjmem))
  ·
    have hjC : coeffEmb ℂ jq = ModularCurve.jqModC ℂ := by
      rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ ℂ)
    have hid := congrArg (coeffEmb ℂ) ModularCurve.thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
    rw [map_mul, map_neg, map_mul, coeffEmb_thetaL, hjC] at hid
    have h4 : coeffEmb ℂ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4)) =
        intSeriesC ℂ eisenstein4 := coeffEmb_intSeriesC ℂ eisenstein4
    have h6 : coeffEmb ℂ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein6)) =
        intSeriesC ℂ eisenstein6 := coeffEmb_intSeriesC ℂ eisenstein6
    rw [h4, h6] at hid
    have hj : ModularCurve.jqModC ℂ ≠ 0 := by
      rw [← hjC]; exact (map_ne_zero (coeffEmb ℂ)).mpr jq_ne_zero
    rw [intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, ← hWint]
    have e4 := hE4ne ℂ
    have e6 := hE6ne ℂ
    field_simp
    linear_combination (-(W ^ 2)) * hid

end S_ModularForm_exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq
end P2MW
export P2MW.S_ModularForm_exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq (solution)
