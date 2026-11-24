-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.norm_F_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:04.871089+00:00
-- url     : https://prove2.me/submissions/30ec0533-3b78-4ad0-a226-93651e2ce0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_one_le
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_one_pos
import Theorems.Thm_GlobalTheory_Hk_RealChar_measurable_th
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_le_integral
import Theorems.Thm_GlobalTheory_Hk_RealChar_wt_nonneg
import Theorems.Thm_GlobalTheory_Hk_RealChar_integrableOn_of_bounds
import Theorems.Thm_GlobalTheory_Hk_RealChar_integral_le
import Theorems.Thm_GlobalTheory_Hk_RealChar_bRe_le
import Theorems.Thm_GlobalTheory_Hk_RealChar_bRe_one
import Theorems.Thm_GlobalTheory_Hk_RealChar_th_eq
import Theorems.Thm_GlobalTheory_T_tsum_exp_mul_aChi_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 →
    c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.tsum_exp_mul_aChi_bounds
  set K := ∫ w in Set.Ioi (0 : ℝ), wt w with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun w hw => wt_nonneg hw
  have hw0 := besW_one_pos
  set w0 := besW 1 with hw0def
  set δ := min 1 (w0 / (2 * (C ^ 2 * K + 1))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : C ^ 2 * K * δ ≤ w0 / 2 := by
    have h1 : δ ≤ w0 / (2 * (C ^ 2 * K + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨((45 : ℕ) : ℝ), min 1 (δ ^ 2 * w0 / 8), by norm_num, by positivity, fun 𝓕 χ hχ => ?_⟩
  rw [Real.rpow_natCast]
  have hB := 𝓕.B_ge
  have hB1 : 1 ≤ 𝓕.B := by linarith
  have hB0 : 0 < 𝓕.B := by linarith
  have hκ : 0 < 𝓕.κ := lt_of_lt_of_le (by positivity) 𝓕.κ_ge
  have hcard : (1 : ℝ) ≤ Fintype.card 𝓕.G := by exact_mod_cast Fintype.card_pos
  by_cases h1 : χ = 1
  · have e : 𝓕.F χ 1 = ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) := by
      simp [LFam.F, LFam.res, h1]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ 1 / 𝓕.B := by
          gcongr
          · exact min_le_left _ _
          · exact le_self_pow₀ hB1 (by norm_num)
      _ ≤ 𝓕.κ := 𝓕.κ_ge
      _ ≤ _ := le_mul_of_one_le_right hκ.le hcard
  have h11 : (1 : AddChar 𝓕.G ℂ) * 1 = 1 := mul_one _
  set ρ := 𝓕.κ * Fintype.card 𝓕.G with hρ
  have hP : ∀ t, 0 < t → |th (bRe 𝓕 1) t - ρ / t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 1).1 t ht).2
    rw [th_eq h11, LFam.res, if_pos rfl, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ : ∀ t, 0 < t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 χ).1 t ht).2
    rw [th_eq hχ, LFam.res, if_neg h1, zero_div, sub_zero,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ' : ∀ t, 1 ≤ t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B * Real.exp (-(t / 2)) := by
    intro t ht
    have := ((H 𝓕 χ).2 h1).1 t ht
    rw [th_eq hχ, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hF : 𝓕.F χ 1 = ((∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t : ℝ) : ℂ) := by
    rw [← ((H 𝓕 χ).2 h1).2]
    simp only [th_eq hχ]
    exact integral_ofReal
  set L := ∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t with hL
  have hE : 0 ≤ C * 𝓕.B ^ 11 := by positivity
  set s := δ / 𝓕.B ^ 22 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 (hδ1.trans (one_le_pow₀ hB1))
  have hv : 0 < s ^ 2 := by positivity
  have hv1 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  have up := integral_le (measurable_th _) (measurable_th _) hE hP hQ
    (integrableOn_of_bounds (measurable_th _) hE hQ hQ') hv
  have lo := besW_le_integral (bRe_le h11) (bRe_le hχ) (bRe_one 𝓕 1) (bRe_one 𝓕 χ)
    (fun n => by simpa [bRe] using (𝓕.sq χ hχ n).1) hv
  have lo' := besW_one_le hv hv1
  rw [Real.sqrt_sq hs0.le, ← hL, ← hK] at up
  have e1 : (C * 𝓕.B ^ 11) ^ 2 * s * K = C ^ 2 * K * δ := by
    rw [hs]; field_simp
  have h2 : w0 / 2 ≤ ρ / s ^ 2 * L := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 4 * 𝓕.B := mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
  have h3 : w0 / 2 ≤ 4 * 𝓕.B / s ^ 2 * |L| :=
    h2.trans ((mul_le_mul_of_nonneg_left (le_abs_self L) (by positivity)).trans (by gcongr))
  rw [hF, Complex.norm_real, Real.norm_eq_abs]
  calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 := by
        gcongr; exact min_le_right _ _
    _ = s ^ 2 / (4 * 𝓕.B) * (w0 / 2) := by rw [hs]; field_simp; norm_num
    _ ≤ s ^ 2 / (4 * 𝓕.B) * (4 * 𝓕.B / s ^ 2 * |L|) := by gcongr
    _ = |L| := by field_simp
end GlobalTheory.Hk.RealChar
