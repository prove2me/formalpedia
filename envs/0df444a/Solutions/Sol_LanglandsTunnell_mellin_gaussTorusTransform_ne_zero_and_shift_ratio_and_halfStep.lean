-- Prove2me | solution 1 for LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7c5e8d36-d73c-5e2c-a644-eb581519c6fd

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
import Theorems.Thm_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
import Theorems.Thm_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel
import Theorems.Thm_LanglandsTunnell_norm_mellin_gaussTorusTransform_halfStep_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep

set_option autoImplicit false

open MeasureTheory Set

open Filter Topology

set_option maxHeartbeats 4000000 in
theorem solution
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ) (hC : C ≠ 0) (p' q' C' : ℂ) (hpq' : (p' + q').re ≤ (p + q).re)
    (H H' H'' : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hH' : H' = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C' * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p' * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q' * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ (κ - 1) * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hH'' : H'' = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ (κ - 2) * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin H (x : ℂ) ≠ 0 ∧
      ‖mellin H ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin H (x : ℂ)‖ ≤ δ * x * ‖mellin H (x : ℂ)‖ ∧
      ‖mellin H' ((x : ℂ) - 1)‖ ≤ δ * ‖mellin H (x : ℂ)‖ ∧
      ‖mellin H'' (x : ℂ)‖ ≤ δ * ‖mellin H (x : ℂ)‖ := by
  intro δ hδ
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hpa : 0 < Real.pi * a ^ 2 := by positivity

  set A : ℂ := κ - 1 - q with hA
  set B : ℂ := p - q - 1 with hB
  set τ : ℝ := q.im / 2 with hτ
  set yof : ℝ → ℝ := fun x => (x + q.re + 1) / 2 with hyof
  set Sof : ℝ → ℂ := fun x => ((x : ℂ) + q + 1) / 2 with hSof
  have hS_eq : ∀ x : ℝ, Sof x = ((yof x : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I := by
    intro x; simp only [hSof, hyof, hτ]; apply Complex.ext <;> simp <;> ring
  set G : ℝ → ℝ → ℝ → ℂ := fun y w r =>
      ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(((y : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
        (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) with hG
  set T : ℝ → ℝ → ℝ → ℝ := fun y w r => (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ A.re * r ^ B.re *
      Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) with hT
  have hnormG : ∀ (y w r : ℝ), 0 < w → 0 < r → ‖G y w r‖ = T y w r := by
    intro y w r hw hr
    have hv : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
    simp only [hG, hT]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hw,
      Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    congr 2
    simp

  set cof : ℝ → ℂ := fun x => 2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-Sof x) * Complex.Gamma (Sof x) with hcof

  have hJF : ∀ x : ℝ, |q.re| + |p.re| + 1 ≤ x →
      mellin H (x : ℂ) = cof x * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G (yof x) w r ∧
      Integrable (fun v : ℝ × ℝ => G (yof x) v.1 v.2)
        (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    intro x hx
    have hzq : -1 < (((x : ℂ)) + q).re := by simp; have := neg_abs_le q.re; have := abs_nonneg p.re; linarith
    have hzp : -1 < (((x : ℂ)) + p).re := by simp; have := neg_abs_le p.re; have := abs_nonneg q.re; linarith
    obtain ⟨-, hI, hM⟩ := LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
      a ha p q κ C H hH (x : ℂ) hzq hzp
    have hexp : -(((x : ℂ) + q + 1) / 2) = -(((yof x : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I) := by
      rw [← hS_eq x]
    refine ⟨?_, ?_⟩
    · rw [hM]; simp only [hcof, hSof, hG, hA, hB, hexp]
    · simpa only [hG, hA, hB, hexp] using hI

  set G2 : ℝ → ℝ → ℝ → ℂ := fun y w r =>
      ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(((y : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ (A - 2) * ((r : ℝ) : ℂ) ^ B *
        (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) with hG2
  have hJF2 : ∀ x : ℝ, |q.re| + |p.re| + 1 ≤ x →
      mellin H'' (x : ℂ) = cof x * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G2 (yof x) w r ∧
      Integrable (fun v : ℝ × ℝ => G2 (yof x) v.1 v.2)
        (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    intro x hx
    have hzq : -1 < (((x : ℂ)) + q).re := by simp; have := neg_abs_le q.re; have := abs_nonneg p.re; linarith
    have hzp : -1 < (((x : ℂ)) + p).re := by simp; have := neg_abs_le p.re; have := abs_nonneg q.re; linarith
    obtain ⟨-, hI, hM⟩ := LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
      a ha p q (κ - 2) C H'' hH'' (x : ℂ) hzq hzp
    have hexp : -(((x : ℂ) + q + 1) / 2) = -(((yof x : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I) := by
      rw [← hS_eq x]
    have hA2 : κ - 2 - 1 - q = A - 2 := by rw [hA]; ring
    refine ⟨?_, ?_⟩
    · rw [hM]; simp only [hcof, hSof, hG2, hB, hexp, hA2]
    · simpa only [hG2, hB, hexp, hA2] using hI

  obtain ⟨R₁, hR₁⟩ := LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral a ha A B τ (1/2) one_half_pos
  set η : ℝ := min (δ * (Real.pi * a ^ 2) / 16) (1/2) with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1/2 := min_le_right _ _
  have hηδ : η ≤ δ * (Real.pi * a ^ 2) / 16 := min_le_left _ _
  obtain ⟨R₂, hR₂⟩ := LanglandsTunnell.exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel a ha A.re B.re η 1 hη0 one_pos
  obtain ⟨R₃, hR₃⟩ := LanglandsTunnell.exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel a ha (A - 2).re B.re η 1 hη0 one_pos

  set ustar : ℝ → ℝ := fun y => (1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) with hustar
  set lw : ℝ → ℝ := fun y => (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ustar y)) / a ^ 2) with hlw
  set lr : ℝ → ℝ := fun y => ustar y - lw y with hlr

  obtain ⟨Rb, hRb⟩ := LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le a ha p q κ C hC p' q' C' hpq' H H' H'' hH hH' hH'' δ hδ

  set Rm : ℝ := max 0 (max R₁ (max R₂ (max R₃ Rb))) with hRm
  have hRm0 : 0 ≤ Rm := le_max_left _ _
  set X₀ : ℝ := |q.re| + |p.re| + ‖q‖ + 2 * Rm + 2 with hX₀
  set Y₀ : ℝ := Real.pi * |a| * Real.exp (3 * (4 - Real.log η) / 2) with hY₀
  set Y₁ : ℝ := Real.pi * |a| * (8 * Real.exp 2 * |a| / δ) ^ 3 with hY₁
  set X₂ : ℝ := 4 * ‖(q + 1) / 2‖ / (δ * (Real.pi * a ^ 2)) with hX₂
  refine ⟨max (max X₀ X₂) (2 * (Y₀ + Y₁) + |q.re| + 1), fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxY : 2 * (Y₀ + Y₁) + |q.re| + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hqn : 0 ≤ ‖q‖ := norm_nonneg _
  have hqa : 0 ≤ |q.re| := abs_nonneg _
  have hpa' : 0 ≤ |p.re| := abs_nonneg _
  have hx0 : |q.re| + |p.re| + 1 ≤ x := by rw [hX₀] at hxX₀; linarith
  have hx2 : |q.re| + |p.re| + 1 ≤ x + 2 := by linarith
  have hxq : ‖q‖ + 1 ≤ x := by rw [hX₀] at hxX₀; linarith
  have hxpos : 0 < x := by have := norm_nonneg q; linarith
  set y : ℝ := yof x with hy
  have hyx : y = (x + q.re + 1) / 2 := rfl
  have hyR : Rm ≤ y := by
    rw [hyx]; rw [hX₀] at hxX₀; have := neg_abs_le q.re; linarith
  have hyR₁ : R₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hyR
  have hyR₂ : R₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hyR
  have hyR₃ : R₃ ≤ y := ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hyR
  have hRb' : Rb ≤ Rm := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hxRb : Rb ≤ x := by rw [hX₀] at hxX₀; linarith
  have hY₀0 : 0 < Y₀ := by rw [hY₀]; positivity
  have hY₁0 : 0 < Y₁ := by rw [hY₁]; positivity
  have hyY₀ : Y₀ ≤ y := by rw [hyx]; have := neg_abs_le q.re; linarith
  have hyY₁ : Y₁ ≤ y := by rw [hyx]; have := neg_abs_le q.re; linarith
  have hypos : 0 < y := hY₀0.trans_le hyY₀
  have hyof2 : yof (x + 2) = y + 1 := by simp only [hy, hyof]; ring

  obtain ⟨hM0, hI0⟩ := hJF x hx0
  obtain ⟨hM1, hI1⟩ := hJF (x + 2) hx2
  obtain ⟨hM2, hI2⟩ := hJF2 x hx0
  rw [hyof2] at hM1 hI1
  have hcast2 : (((x + 2 : ℝ)) : ℂ) = (x : ℂ) + 2 := by push_cast; ring
  rw [hcast2] at hM1

  set μp : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμp
  set μ2 : Measure (ℝ × ℝ) := μp.prod μp with hμ2
  set F0 : ℝ × ℝ → ℂ := fun v => G y v.1 v.2 with hF0
  set F1 : ℝ × ℝ → ℂ := fun v => G (y + 1) v.1 v.2 with hF1
  set F2 : ℝ × ℝ → ℂ := fun v => G2 y v.1 v.2 with hF2
  have hI0' : Integrable F0 μ2 := hI0
  have hI1' : Integrable F1 μ2 := hI1
  have hI2' : Integrable F2 μ2 := hI2
  have hII0 : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G y w r) = ∫ v, F0 v ∂μ2 := by rw [hμ2, integral_prod _ hI0']
  have hII1 : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G (y + 1) w r) = ∫ v, F1 v ∂μ2 := by rw [hμ2, integral_prod _ hI1']
  have hII2 : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G2 y w r) = ∫ v, F2 v ∂μ2 := by rw [hμ2, integral_prod _ hI2']
  have hNN : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G y w r‖) = ∫ v, ‖F0 v‖ ∂μ2 := by rw [hμ2, integral_prod _ hI0'.norm]
  set N : ℝ := ∫ v, ‖F0 v‖ ∂μ2 with hN
  have hN0 : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)

  have hcoh : (1 - 1/2) * N ≤ ‖∫ v, F0 v ∂μ2‖ := by
    have h := hR₁ y hyR₁
    rw [hNN, hII0] at h
    exact h
  have hNle : N ≤ 2 * ‖∫ v, F0 v ∂μ2‖ := by linarith

  have hae : ∀ᵐ v ∂μ2, v ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    rw [hμ2, hμp, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

  set Bw : Set ℝ := Icc (Real.exp (lw y - 1)) (Real.exp (lw y + 1)) with hBw
  set Br : Set ℝ := Icc (Real.exp (lr y - 1)) (Real.exp (lr y + 1)) with hBr
  have hBw_sub : Bw ⊆ Ioi 0 := fun w hw => (Real.exp_pos _).trans_le hw.1
  have hBr_sub : Br ⊆ Ioi 0 := fun r hr => (Real.exp_pos _).trans_le hr.1
  set Sb : Set (ℝ × ℝ) := Bw ×ˢ Br with hSb
  have hSm : MeasurableSet Sb := measurableSet_Icc.prod measurableSet_Icc
  have hrestr : μ2.restrict Sb = (volume.restrict Bw).prod (volume.restrict Br) := by
    rw [hμ2, hμp, hSb, ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hBw_sub, inter_eq_left.mpr hBr_sub]

  have hconc0 : (1 - η) * N ≤ ∫ v in Sb, ‖F0 v‖ ∂μ2 := by
    have h := hR₂ y hyR₂
    have hl : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T y w r) = N := by
      have e : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T y w r) = ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G y w r‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_))
        exact (hnormG y w r hw hr).symm
      rw [e]; exact hNN
    have hr' : (∫ w in Bw, ∫ r in Br, T y w r) = ∫ v in Sb, ‖F0 v‖ ∂μ2 := by
      rw [hrestr, integral_prod _ (hI0'.norm.mono_measure (by rw [← hrestr]; exact Measure.restrict_le_self))]
      refine setIntegral_congr_fun measurableSet_Icc (fun w hw => setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_))
      exact (hnormG y w r (hBw_sub hw) (hBr_sub hr)).symm
    have h' : (1 - η) * (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T y w r) ≤ ∫ w in Bw, ∫ r in Br, T y w r := by
      simpa only [hT, hBw, hBr, hlw, hlr, hustar] using h
    rwa [hl, hr'] at h'
  have htail0 : ∫ v in Sbᶜ, ‖F0 v‖ ∂μ2 ≤ η * N := by
    have hsplit := integral_add_compl hSm hI0'.norm
    rw [← hN] at hsplit; linarith

  set N2 : ℝ := ∫ v, ‖F2 v‖ ∂μ2 with hN2
  have hnormG2 : ∀ (w r : ℝ), 0 < w → 0 < r → ‖G2 y w r‖ = T y w r * w ^ (-(2:ℝ)) := by
    intro w r hw hr
    have hv : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
    simp only [hG2, hT]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hw,
      Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
      Complex.sub_re, Real.rpow_sub hw, Real.rpow_neg hw.le]
    have : (-(((y:ℝ):ℂ) + ((τ:ℝ):ℂ) * Complex.I)).re = -y := by simp
    rw [this]
    have h2 : ((2:ℂ)).re = 2 := by simp
    rw [h2, Real.rpow_two]; ring
  have hconc2 : (1 - η) * N2 ≤ ∫ v in Sb, ‖F2 v‖ ∂μ2 := by
    have h := hR₃ y hyR₃
    have hN2N : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G2 y w r‖) = N2 := by rw [hN2, hμ2, integral_prod _ hI2'.norm]
    have hTA : ∀ w r : ℝ, 0 < w → 0 < r → (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ (A - 2).re * r ^ B.re *
        Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) = ‖G2 y w r‖ := by
      intro w r hw hr
      rw [hnormG2 w r hw hr]; simp only [hT, Complex.sub_re]
      have h2 : ((2:ℂ)).re = 2 := by simp
      rw [h2, Real.rpow_sub hw, Real.rpow_neg hw.le, Real.rpow_two]; ring
    have hl : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ (A - 2).re * r ^ B.re *
        Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) = N2 := by
      rw [← hN2N]
      exact setIntegral_congr_fun measurableSet_Ioi (fun w hw => setIntegral_congr_fun measurableSet_Ioi (fun r hr => hTA w r hw hr))
    have hr' : (∫ w in Bw, ∫ r in Br, (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ (A - 2).re * r ^ B.re *
        Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) = ∫ v in Sb, ‖F2 v‖ ∂μ2 := by
      rw [hrestr, integral_prod _ (hI2'.norm.mono_measure (by rw [← hrestr]; exact Measure.restrict_le_self))]
      exact setIntegral_congr_fun measurableSet_Icc (fun w hw => setIntegral_congr_fun measurableSet_Icc
        (fun r hr => hTA w r (hBw_sub hw) (hBr_sub hr)))
    have h'' : (1 - η) * (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ (A - 2).re * r ^ B.re *
        Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) ≤
        ∫ w in Bw, ∫ r in Br, (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ (A - 2).re * r ^ B.re *
        Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by
      simpa only [hBw, hBr, hlw, hlr, hustar] using h
    rwa [hl, hr'] at h''

  have hF1eq : ∀ v : ℝ × ℝ, v ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) →
      F1 v = ((((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ))⁻¹ * F0 v := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    have hw0 : (0:ℝ) < w := hw
    have hr0 : (0:ℝ) < r := hr
    have hv : (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ≠ 0 := by
      have : (0:ℝ) < 1 + ((w * r) ^ 2)⁻¹ := by positivity
      exact_mod_cast this.ne'
    simp only [hF1, hF0, hG]
    have : -((((y + 1 : ℝ)) : ℂ) + ((τ:ℝ):ℂ) * Complex.I) = -(((y:ℝ):ℂ) + ((τ:ℝ):ℂ) * Complex.I) + (-1) := by push_cast; ring
    rw [this, Complex.cpow_add _ _ hv, Complex.cpow_neg_one]; ring
  have hdiff_norm : ∀ v : ℝ × ℝ, v ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) →
      ‖F1 v - F0 v‖ = (1 - (1 + ((v.1 * v.2) ^ 2)⁻¹)⁻¹) * ‖F0 v‖ := by
    intro v hv
    have ht : 0 < 1 + ((v.1 * v.2) ^ 2)⁻¹ := by positivity
    rw [hF1eq v hv, ← sub_one_mul, norm_mul]
    congr 1
    rw [show ((((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ))⁻¹ - 1 = ((((1 + ((v.1 * v.2) ^ 2)⁻¹)⁻¹ - 1 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos, neg_sub]
    rw [sub_nonpos]
    have : 0 ≤ ((v.1 * v.2) ^ 2)⁻¹ := by positivity
    exact inv_le_one_of_one_le₀ (by linarith)
  have hone_sub_le : ∀ t : ℝ, 0 ≤ t → 1 - (1 + t)⁻¹ ≤ t := by
    intro t ht
    have h1 : 0 < 1 + t := by linarith
    have e : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
    rw [e, div_le_iff₀ h1]
    nlinarith

  have hθ_box : ∀ v : ℝ × ℝ, v ∈ Sb → ((v.1 * v.2) ^ 2)⁻¹ ≤ Real.exp (4 - 2 * ustar y) := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    have hw1 : Real.exp (lw y - 1) ≤ w := hw.1
    have hr1 : Real.exp (lr y - 1) ≤ r := hr.1
    have hprod : Real.exp (ustar y - 2) ≤ w * r := by
      have : Real.exp (lw y - 1) * Real.exp (lr y - 1) = Real.exp (ustar y - 2) := by
        rw [← Real.exp_add]; congr 1; simp only [hlr]; ring
      rw [← this]; exact mul_le_mul hw1 hr1 (Real.exp_pos _).le ((Real.exp_pos _).le.trans hw1)
    have hpos : 0 < Real.exp (ustar y - 2) := Real.exp_pos _
    have h2 : Real.exp (ustar y - 2) ^ 2 ≤ (w * r) ^ 2 := pow_le_pow_left₀ hpos.le hprod 2
    calc ((w * r) ^ 2)⁻¹ ≤ (Real.exp (ustar y - 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
      _ = Real.exp (4 - 2 * ustar y) := by rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hw_box : ∀ v : ℝ × ℝ, v ∈ Sb → v.1 ^ (-(2:ℝ)) ≤ Real.exp (2 - 2 * lw y) := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    have hw1 : Real.exp (lw y - 1) ≤ w := hw.1
    have hwpos : 0 < w := (Real.exp_pos _).trans_le hw1
    rw [Real.rpow_neg hwpos.le, Real.rpow_two]
    calc (w ^ 2)⁻¹ ≤ (Real.exp (lw y - 1) ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ (Real.exp_pos _).le hw1 2)
      _ = Real.exp (2 - 2 * lw y) := by rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring

  set θ : ℝ := Real.exp (4 - 2 * ustar y) with hθ
  have hθη : θ ≤ η := by

    have hyq : Real.exp (3 * (4 - Real.log η) / 2) ≤ y / (Real.pi * |a|) := by
      rw [le_div_iff₀ (by positivity)]; rw [hY₀] at hyY₀; linarith
    have hu : (4 - Real.log η) / 2 ≤ ustar y := by
      simp only [hustar]
      have := Real.log_le_log (Real.exp_pos _) hyq
      rw [Real.log_exp] at this; linarith
    rw [hθ, ← Real.exp_log hη0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcfac : 4 * Real.exp (2 - 2 * lw y) ≤ δ := by

    have hlw_ge : ustar y / 2 - Real.log |a| / 2 ≤ lw y := by
      simp only [hlw]
      have h1 : Real.exp (2 * ustar y) / a ^ 2 ≤ (1 + Real.exp (2 * ustar y)) / a ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [Real.exp_pos (2 * ustar y)]) (by positivity)
      have h2 := Real.log_le_log (by positivity) h1
      have hla : Real.log (a ^ 2) = 2 * Real.log |a| := by
        rw [← sq_abs, Real.log_pow]; push_cast; ring
      rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp, hla] at h2
      linarith
    have hyq : (8 * Real.exp 2 * |a| / δ) ^ 3 ≤ y / (Real.pi * |a|) := by
      rw [le_div_iff₀ (by positivity)]; rw [hY₁] at hyY₁; linarith
    have hK : 0 < 8 * Real.exp 2 * |a| / δ := by positivity
    have hu : 3 * Real.log (8 * Real.exp 2 * |a| / δ) ≤ Real.log (y / (Real.pi * |a|)) := by
      have := Real.log_le_log (by positivity) hyq
      rwa [Real.log_pow] at this
    have hu' : Real.log (8 * Real.exp 2 * |a| / δ) ≤ ustar y := by simp only [hustar]; linarith

    have h3 : Real.exp (2 - 2 * lw y) ≤ Real.exp 2 * |a| * Real.exp (-ustar y) := by
      rw [← Real.exp_log ha0, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-ustar y) ≤ δ / (8 * Real.exp 2 * |a|) := by
      rw [← Real.exp_log (by positivity : 0 < δ / (8 * Real.exp 2 * |a|))]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div hδ.ne' (by positivity)]
      have : Real.log (8 * Real.exp 2 * |a| / δ) = Real.log (8 * Real.exp 2 * |a|) - Real.log δ :=
        Real.log_div (by positivity) hδ.ne'
      linarith
    calc 4 * Real.exp (2 - 2 * lw y) ≤ 4 * (Real.exp 2 * |a| * Real.exp (-ustar y)) := by linarith
      _ ≤ 4 * (Real.exp 2 * |a| * (δ / (8 * Real.exp 2 * |a|))) := by gcongr
      _ = δ / 2 := by field_simp; ring
      _ ≤ δ := by linarith

  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hdiff : ‖(∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2‖ ≤ (θ + η) * N := by
    rw [← integral_sub hI1' hI0']
    refine (norm_integral_le_integral_norm _).trans ?_
    have hDn : Integrable (fun v => ‖F1 v - F0 v‖) μ2 := (hI1'.sub hI0').norm
    have hsplit := integral_add_compl hSm hDn
    rw [← hsplit]
    have hS_part : ∫ v in Sb, ‖F1 v - F0 v‖ ∂μ2 ≤ θ * ∫ v in Sb, ‖F0 v‖ ∂μ2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hDn.integrableOn (hI0'.norm.const_mul θ).integrableOn hSm (fun v hv => ?_)
      have hvq : v ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := ⟨hBw_sub hv.1, hBr_sub hv.2⟩
      rw [hdiff_norm v hvq]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (hone_sub_le _ (by positivity)).trans (hθ_box v hv)
    have hSc_part : ∫ v in Sbᶜ, ‖F1 v - F0 v‖ ∂μ2 ≤ ∫ v in Sbᶜ, ‖F0 v‖ ∂μ2 := by
      refine integral_mono_ae hDn.integrableOn hI0'.norm.integrableOn ?_
      refine (ae_restrict_of_ae hae).mono (fun v hv => ?_)
      show ‖F1 v - F0 v‖ ≤ ‖F0 v‖
      rw [hdiff_norm v hv]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      have : 0 ≤ (1 + ((v.1 * v.2) ^ 2)⁻¹)⁻¹ := by positivity
      linarith
    have hSle : ∫ v in Sb, ‖F0 v‖ ∂μ2 ≤ N := by
      rw [hN]; exact setIntegral_le_integral hI0'.norm (ae_of_all _ (fun _ => norm_nonneg _))
    calc (∫ v in Sb, ‖F1 v - F0 v‖ ∂μ2) + ∫ v in Sbᶜ, ‖F1 v - F0 v‖ ∂μ2
        ≤ θ * (∫ v in Sb, ‖F0 v‖ ∂μ2) + ∫ v in Sbᶜ, ‖F0 v‖ ∂μ2 := add_le_add hS_part hSc_part
      _ ≤ θ * N + η * N := add_le_add (mul_le_mul_of_nonneg_left hSle hθ0) htail0
      _ = (θ + η) * N := by ring

  have hc_est : ‖∫ v, F2 v ∂μ2‖ ≤ 4 * Real.exp (2 - 2 * lw y) * ‖∫ v, F0 v ∂μ2‖ := by
    have h1 : ‖∫ v, F2 v ∂μ2‖ ≤ N2 := norm_integral_le_integral_norm _
    have h2 : ∫ v in Sb, ‖F2 v‖ ∂μ2 ≤ Real.exp (2 - 2 * lw y) * ∫ v in Sb, ‖F0 v‖ ∂μ2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hI2'.norm.integrableOn (hI0'.norm.const_mul _).integrableOn hSm (fun v hv => ?_)
      have hw0 : 0 < v.1 := hBw_sub hv.1
      have hr0 : 0 < v.2 := hBr_sub hv.2
      show ‖G2 y v.1 v.2‖ ≤ Real.exp (2 - 2 * lw y) * ‖G y v.1 v.2‖
      rw [hnormG2 v.1 v.2 hw0 hr0, hnormG y v.1 v.2 hw0 hr0, mul_comm]
      exact mul_le_mul_of_nonneg_right (hw_box v hv) (by rw [← hnormG y v.1 v.2 hw0 hr0]; exact norm_nonneg _)
    have hSle : ∫ v in Sb, ‖F0 v‖ ∂μ2 ≤ N := by
      rw [hN]; exact setIntegral_le_integral hI0'.norm (ae_of_all _ (fun _ => norm_nonneg _))
    have hN2le : N2 ≤ 2 * (Real.exp (2 - 2 * lw y) * N) := by
      have : (1 - η) * N2 ≤ Real.exp (2 - 2 * lw y) * N := hconc2.trans (h2.trans (mul_le_mul_of_nonneg_left hSle (Real.exp_pos _).le))
      have hN20 : 0 ≤ N2 := integral_nonneg (fun _ => norm_nonneg _)
      nlinarith [hη1]
    calc ‖∫ v, F2 v ∂μ2‖ ≤ N2 := h1
      _ ≤ 2 * (Real.exp (2 - 2 * lw y) * N) := hN2le
      _ ≤ 2 * (Real.exp (2 - 2 * lw y) * (2 * ‖∫ v, F0 v ∂μ2‖)) := by gcongr
      _ = _ := by ring

  have hNpos : 0 < N := by
    rw [hN, integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun _ => norm_nonneg _)) hI0'.norm]
    have hsub : Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) ⊆ Function.support (fun v : ℝ × ℝ => ‖F0 v‖) := by
      rintro ⟨w, r⟩ ⟨hw, hr⟩
      have hw0 : (0:ℝ) < w := hw
      have hr0 : (0:ℝ) < r := hr
      rw [Function.mem_support, hF0]
      show ‖G y w r‖ ≠ 0
      rw [hnormG y w r hw0 hr0]; simp only [hT]
      have : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [hμ2, Measure.prod_prod, hμp, Measure.restrict_apply' measurableSet_Ioi, inter_self, Real.volume_Ioi]
    simp
  have hI0ne : (∫ v, F0 v ∂μ2) ≠ 0 := by
    intro h; rw [h, norm_zero] at hNle; linarith
  have hS_re : (Sof x).re = y := by rw [hy, hS_eq]; simp
  have hS0 : Sof x ≠ 0 := by intro h; have := congrArg Complex.re h; rw [hS_re] at this; simp at this; linarith
  have hcof0 : cof x ≠ 0 := by
    simp only [hcof]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hC) ?_) ?_) ?_
    · intro h; rw [Complex.cpow_eq_zero_iff] at h; exact absurd h.1 (by exact_mod_cast ha0.ne')
    · intro h; rw [Complex.cpow_eq_zero_iff] at h; exact absurd h.1 (by exact_mod_cast hpa.ne')
    · exact Complex.Gamma_ne_zero_of_re_pos (by rw [hS_re]; exact hypos)

  have hS2 : Sof (x + 2) = Sof x + 1 := by simp only [hSof]; push_cast; ring
  have hpaC : (((Real.pi * a ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpa.ne'
  have hcof2 : cof (x + 2) = cof x * ((((Real.pi * a ^ 2 : ℝ)) : ℂ))⁻¹ * Sof x := by
    simp only [hcof]
    rw [hS2, Complex.Gamma_add_one _ hS0, neg_add, Complex.cpow_add _ _ hpaC, Complex.cpow_neg_one]
    ring
  have hSq : Sof x - (x : ℂ) / 2 = (q + 1) / 2 := by simp only [hSof]; ring
  have hSnorm : ‖Sof x‖ ≤ x := by
    simp only [hSof]
    rw [norm_div, Complex.norm_two]
    have : ‖(x : ℂ) + q + 1‖ ≤ x + ‖q‖ + 1 := by
      calc ‖(x : ℂ) + q + 1‖ ≤ ‖(x : ℂ) + q‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ ‖(x : ℂ)‖ + ‖q‖ + ‖(1:ℂ)‖ := by gcongr; exact norm_add_le _ _
        _ = x + ‖q‖ + 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hxpos.le, norm_one]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith
  have hq1 : ‖(q + 1) / 2‖ ≤ δ * (Real.pi * a ^ 2) * x / 4 := by
    rw [hX₂] at hxX₂
    rw [div_le_iff₀ (by positivity)] at hxX₂
    linarith
  have hcofn : 0 ≤ ‖cof x‖ := norm_nonneg _
  have hI0n : 0 ≤ ‖∫ v, F0 v ∂μ2‖ := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hM0, hII0]; exact mul_ne_zero hcof0 hI0ne
  ·
    rw [hM1, hM0, hII1, hII0, hcof2]
    generalize hcg : cof x = c0
    have hc0n : 0 ≤ ‖c0‖ := norm_nonneg _
    have hfrac : (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) = ((((Real.pi * a ^ 2 : ℝ)) : ℂ))⁻¹ * ((x : ℂ) / 2) := by
      push_cast; field_simp
    rw [hfrac]
    have e : c0 * ((((Real.pi * a ^ 2 : ℝ)) : ℂ))⁻¹ * Sof x * (∫ v, F1 v ∂μ2)
        - ((((Real.pi * a ^ 2 : ℝ)) : ℂ))⁻¹ * ((x : ℂ) / 2) * (c0 * ∫ v, F0 v ∂μ2)
        = c0 * ((((Real.pi * a ^ 2 : ℝ)) : ℂ))⁻¹ *
          (Sof x * ((∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2) + (Sof x - (x : ℂ) / 2) * ∫ v, F0 v ∂μ2) := by ring
    rw [e, hSq, norm_mul (c0 * _), norm_mul c0, norm_mul c0, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpa.le]
    have hin : ‖Sof x * ((∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2) + (q + 1) / 2 * ∫ v, F0 v ∂μ2‖
        ≤ x * ((θ + η) * N) + δ * (Real.pi * a ^ 2) * x / 4 * ‖∫ v, F0 v ∂μ2‖ := by
      calc _ ≤ ‖Sof x * ((∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2)‖ + ‖(q + 1) / 2 * ∫ v, F0 v ∂μ2‖ := norm_add_le _ _
        _ = ‖Sof x‖ * ‖(∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2‖ + ‖(q + 1) / 2‖ * ‖∫ v, F0 v ∂μ2‖ := by rw [norm_mul, norm_mul]
        _ ≤ x * ((θ + η) * N) + δ * (Real.pi * a ^ 2) * x / 4 * ‖∫ v, F0 v ∂μ2‖ := by
            gcongr
    have hθη2 : (θ + η) * N ≤ 2 * η * (2 * ‖∫ v, F0 v ∂μ2‖) := by
      calc (θ + η) * N ≤ (2 * η) * N := by nlinarith [hθη, hN0]
        _ ≤ 2 * η * (2 * ‖∫ v, F0 v ∂μ2‖) := mul_le_mul_of_nonneg_left hNle (by positivity)
    have hxin : x * ((θ + η) * N) ≤ x * (2 * η * (2 * ‖∫ v, F0 v ∂μ2‖)) := mul_le_mul_of_nonneg_left hθη2 hxpos.le
    calc ‖c0‖ * (Real.pi * a ^ 2)⁻¹ * ‖Sof x * ((∫ v, F1 v ∂μ2) - ∫ v, F0 v ∂μ2) + (q + 1) / 2 * ∫ v, F0 v ∂μ2‖
        ≤ ‖c0‖ * (Real.pi * a ^ 2)⁻¹ * (x * (2 * η * (2 * ‖∫ v, F0 v ∂μ2‖)) + δ * (Real.pi * a ^ 2) * x / 4 * ‖∫ v, F0 v ∂μ2‖) := by
          gcongr
          exact hin.trans (by linarith)
      _ = (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) * x * ((Real.pi * a ^ 2)⁻¹ * (4 * η) + δ / 4) := by
          field_simp; ring
      _ ≤ (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) * x * (δ / 4 + δ / 4) := by
          gcongr
          rw [inv_mul_le_iff₀ hpa]; linarith
      _ ≤ δ * x * (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) := by
          have hP : 0 ≤ (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) * x * δ := by positivity
          linarith
  ·
    exact hRb x hxRb
  ·
    rw [hM2, hM0, hII2, hII0]
    generalize hcg : cof x = c0
    have hc0n : 0 ≤ ‖c0‖ := norm_nonneg _
    rw [norm_mul c0, norm_mul c0]
    calc ‖c0‖ * ‖∫ v, F2 v ∂μ2‖ ≤ ‖c0‖ * (4 * Real.exp (2 - 2 * lw y) * ‖∫ v, F0 v ∂μ2‖) :=
          mul_le_mul_of_nonneg_left hc_est hc0n
      _ = (4 * Real.exp (2 - 2 * lw y)) * (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) := by ring
      _ ≤ δ * (‖c0‖ * ‖∫ v, F0 v ∂μ2‖) := mul_le_mul_of_nonneg_right hcfac (mul_nonneg hc0n hI0n)

end S_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep
end P2MW
export P2MW.S_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep (solution)
