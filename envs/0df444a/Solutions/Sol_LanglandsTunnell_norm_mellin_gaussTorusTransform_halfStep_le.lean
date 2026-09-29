-- Prove2me | solution 1 for LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/14ee5f8d-a023-52f0-8ee3-0bea513ef2d6

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
import Theorems.Thm_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
import Theorems.Thm_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel
import Theorems.Thm_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_mellin_gaussTorusTransform_halfStep_le

set_option autoImplicit false

open MeasureTheory Set

open Filter Topology

namespace OcBoxRatio

theorem rpow_le_two_rpow_abs {x s : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : x ^ s ≤ (2:ℝ) ^ |s| := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact Real.rpow_le_rpow (by linarith) h2 hs
  · rw [abs_of_neg hs]
    calc x ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 hs.le
      _ ≤ (2:ℝ) ^ (-s) := Real.one_le_rpow (by norm_num) (by linarith)

theorem rpow_le_exp_mul_rpow {w ℓ : ℝ} (hw0 : 0 < w) (hlo : ℓ - 1 ≤ Real.log w) (hhi : Real.log w ≤ ℓ + 1) (α α' : ℝ) :
    w ^ α' ≤ Real.exp ((α' - α) * ℓ + |α' - α|) * w ^ α := by
  rw [show α' = α + (α' - α) by ring, Real.rpow_add hw0, mul_comm, show α + (α' - α) - α = α' - α by ring]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hw0.le _)
  rw [Real.rpow_def_of_pos hw0]
  refine Real.exp_le_exp.2 ?_
  have : |Real.log w - ℓ| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h := abs_mul (α' - α) (Real.log w - ℓ)
  have : |(α' - α) * (Real.log w - ℓ)| ≤ |α' - α| * 1 := by rw [h]; exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have := le_abs_self ((α' - α) * (Real.log w - ℓ))
  nlinarith

end OcBoxRatio

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral exists_forall_mul_integral_norm_tiltKernel_le_norm_integral exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma" end LanglandsTunnell
p2m_open_scoped "LanglandsTunnell" in
theorem LanglandsTunnell.tiltKernel_le_mul_tiltKernel_of_mem_logBox
    (a : ℝ) (ha : a ≠ 0) (y y' α β α' β' : ℝ) (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hθ : Real.exp (4 - 2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|)))) ≤ 1)
    (w r : ℝ)
    (hw : w ∈ Icc (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2) - 1))
                  (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2) + 1)))
    (hr : r ∈ Icc (Real.exp (((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2)) - 1))
                  (Real.exp (((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2)) + 1))) :
    (1 + ((w * r) ^ 2)⁻¹) ^ (-y') * w ^ α' * r ^ β' * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))
      ≤ (2 : ℝ) ^ |y - y'| *
        Real.exp ((α' - α) * ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2))
                + (β' - β) * (((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y' / (Real.pi * |a|))))) / a ^ 2)))
                + |α' - α| + |β' - β|) *
        ((1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) := by
  set u : ℝ := (1/3 : ℝ) * Real.log (y' / (Real.pi * |a|)) with hu
  set ℓw : ℝ := (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2) with hℓw
  set ℓr : ℝ := u - ℓw with hℓr
  set E : ℝ := Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) with hE
  set t : ℝ := ((w * r) ^ 2)⁻¹ with ht

  have hw0 : 0 < w := lt_of_lt_of_le (Real.exp_pos _) hw.1
  have hr0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) hr.1
  have hlw_lo : ℓw - 1 ≤ Real.log w := by rw [Real.le_log_iff_exp_le hw0]; exact hw.1
  have hlw_hi : Real.log w ≤ ℓw + 1 := by rw [Real.log_le_iff_le_exp hw0]; exact hw.2
  have hlr_lo : ℓr - 1 ≤ Real.log r := by rw [Real.le_log_iff_exp_le hr0]; exact hr.1
  have hlr_hi : Real.log r ≤ ℓr + 1 := by rw [Real.log_le_iff_le_exp hr0]; exact hr.2

  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hwr : Real.exp (u - 2) ≤ w * r := by
    have := mul_le_mul hw.1 hr.1 (Real.exp_pos _).le hw0.le
    rw [← Real.exp_add] at this
    rw [show u - 2 = (ℓw - 1) + (ℓr - 1) by rw [hℓr]; ring]; exact this
  have ht1 : t ≤ 1 := by
    have h1 : Real.exp (u - 2) ^ 2 ≤ (w * r) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hwr 2
    have h2 : ((w * r) ^ 2)⁻¹ ≤ (Real.exp (u - 2) ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]; exact h1
    have h3 : (Real.exp (u - 2) ^ 2)⁻¹ = Real.exp (4 - 2 * u) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
    rw [ht]; linarith [h2.trans_eq h3, hθ]

  have hA : (1 + t) ^ (-y') ≤ (2:ℝ) ^ |y - y'| * (1 + t) ^ (-y) := by
    have h1t : 0 < 1 + t := by linarith
    rw [show -y' = -y + (y - y') by ring, Real.rpow_add h1t, mul_comm]
    exact mul_le_mul_of_nonneg_right (OcBoxRatio.rpow_le_two_rpow_abs (by linarith) (by linarith)) (Real.rpow_nonneg h1t.le _)
  have hB := OcBoxRatio.rpow_le_exp_mul_rpow hw0 hlw_lo hlw_hi α α'
  have hC := OcBoxRatio.rpow_le_exp_mul_rpow hr0 hlr_lo hlr_hi β β'
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have h1t0 : 0 ≤ (1 + t) ^ (-y) := Real.rpow_nonneg (by linarith) _

  show (1 + t) ^ (-y') * w ^ α' * r ^ β' * E ≤ (2:ℝ) ^ |y - y'| * Real.exp ((α' - α) * ℓw + (β' - β) * ℓr + |α' - α| + |β' - β|) * ((1 + t) ^ (-y) * w ^ α * r ^ β * E)
  calc (1 + t) ^ (-y') * w ^ α' * r ^ β' * E
      ≤ ((2:ℝ) ^ |y - y'| * (1 + t) ^ (-y)) * (Real.exp ((α' - α) * ℓw + |α' - α|) * w ^ α) * (Real.exp ((β' - β) * ℓr + |β' - β|) * r ^ β) * E := by
        refine mul_le_mul_of_nonneg_right ?_ hE0
        refine mul_le_mul (mul_le_mul hA hB (Real.rpow_nonneg hw0.le _) (by positivity)) hC (Real.rpow_nonneg hr0.le _) (by positivity)
    _ = (2:ℝ) ^ |y - y'| * Real.exp ((α' - α) * ℓw + (β' - β) * ℓr + |α' - α| + |β' - β|) * ((1 + t) ^ (-y) * w ^ α * r ^ β * E) := by
        have hXY : Real.exp ((α' - α) * ℓw + (β' - β) * ℓr + |α' - α| + |β' - β|)
            = Real.exp ((α' - α) * ℓw + |α' - α|) * Real.exp ((β' - β) * ℓr + |β' - β|) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hXY]; ring

p2m_open_scoped "LanglandsTunnell" in
theorem LanglandsTunnell.halfStep_logBook
    (d Δα Δβ la lpa M₀ δ y y' u' lw' : ℝ)
    (hM₀ : 0 < M₀) (hδ : 0 < δ) (hy : 1 ≤ y) (hy' : 0 < y') (hlo : y / 2 ≤ y') (hhi : y' ≤ 2 * y)
    (hkey : d + (Δα + Δβ) / 6 ≤ -(2/3 : ℝ))
    (hu' : u' = (1/3 : ℝ) * (Real.log y' - lpa))
    (hlw_lo : u' / 2 - la / 2 ≤ lw') (hlw_hi : lw' ≤ u' / 2 - la / 2 + Real.log 2 / 4)
    (hY : Real.exp ((3/2 : ℝ) * (Real.log M₀
            + (|Δα - Δβ| * ((abs la) / 2 + Real.log 2 / 4) + |Δα| + |Δβ| + |Δα + Δβ| / 6 * ((abs lpa) + Real.log 2))
            - Real.log δ)) ≤ y) :
    M₀ * y ^ d * Real.exp (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|) ≤ δ := by
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₂ : ℝ := |Δα - Δβ| * ((abs la) / 2 + Real.log 2 / 4) + |Δα| + |Δβ| + |Δα + Δβ| / 6 * ((abs lpa) + Real.log 2) with hC₂

  have hY' : (3/2 : ℝ) * (Real.log M₀ + C₂ - Real.log δ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hY
    rwa [Real.log_exp] at this

  have hlog_hi : Real.log y' ≤ Real.log y + Real.log 2 := by
    have := Real.log_le_log hy' hhi
    rwa [Real.log_mul (by norm_num) hy0.ne', add_comm] at this
  have hlog_lo : Real.log y - Real.log 2 ≤ Real.log y' := by
    have := Real.log_le_log (by linarith) hlo
    rwa [Real.log_div hy0.ne' (by norm_num)] at this

  set c : ℝ := lw' - (u' / 2 - la / 2) with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c ≤ Real.log 2 / 4 := by rw [hc]; linarith

  have h1 : Δα * lw' + Δβ * (u' - lw') ≤ (Δα + Δβ) * u' / 2 + |Δα - Δβ| * ((abs la) / 2 + Real.log 2 / 4) := by
    have e : Δα * lw' + Δβ * (u' - lw') = (Δα + Δβ) * u' / 2 + (Δβ - Δα) * (la / 2) + (Δα - Δβ) * c := by
      rw [hc]; ring
    rw [e]
    have t1 : (Δβ - Δα) * (la / 2) ≤ |Δα - Δβ| * ((abs la) / 2) := by
      have := abs_mul (Δβ - Δα) (la / 2)
      rw [abs_sub_comm, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] at this
      linarith [le_abs_self ((Δβ - Δα) * (la / 2))]
    have t2 : (Δα - Δβ) * c ≤ |Δα - Δβ| * (Real.log 2 / 4) := by
      calc (Δα - Δβ) * c ≤ |Δα - Δβ| * c := mul_le_mul_of_nonneg_right (le_abs_self _) hc0
        _ ≤ |Δα - Δβ| * (Real.log 2 / 4) := mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
    nlinarith

  have h2 : (Δα + Δβ) * u' / 2 ≤ (Δα + Δβ) / 6 * Real.log y + |Δα + Δβ| / 6 * ((abs lpa) + Real.log 2) := by
    rw [hu']
    have e : (Δα + Δβ) * ((1/3 : ℝ) * (Real.log y' - lpa)) / 2
        = (Δα + Δβ) / 6 * Real.log y + (Δα + Δβ) / 6 * ((Real.log y' - Real.log y) + (-lpa)) := by ring
    rw [e]
    have hdiff : |(Real.log y' - Real.log y) + (-lpa)| ≤ Real.log 2 + abs lpa := by
      refine (abs_add_le _ _).trans (add_le_add ?_ (by rw [abs_neg]))
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have : (Δα + Δβ) / 6 * ((Real.log y' - Real.log y) + (-lpa)) ≤ |Δα + Δβ| / 6 * ((abs lpa) + Real.log 2) := by
      have h := abs_mul ((Δα + Δβ) / 6) ((Real.log y' - Real.log y) + (-lpa))
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 6)] at h
      have := le_abs_self ((Δα + Δβ) / 6 * ((Real.log y' - Real.log y) + (-lpa)))
      have := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ |Δα + Δβ| / 6)
      linarith
    linarith

  have h3 : (d + (Δα + Δβ) / 6) * Real.log y ≤ -(2/3 : ℝ) * Real.log y := mul_le_mul_of_nonneg_right hkey hlogy

  have hlog : Real.log M₀ + d * Real.log y + (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|) ≤ Real.log δ := by
    have : Real.log M₀ + d * Real.log y + (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|)
        ≤ Real.log M₀ + C₂ + (d + (Δα + Δβ) / 6) * Real.log y := by rw [hC₂]; nlinarith
    nlinarith

  have e : M₀ * y ^ d * Real.exp (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|)
      = Real.exp (Real.log M₀ + d * Real.log y + (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|)) := by
    rw [Real.exp_add (Real.log M₀ + d * Real.log y), Real.exp_add (Real.log M₀), Real.exp_log hM₀,
      Real.rpow_def_of_pos hy0, mul_comm (Real.log y) d]
  rw [e]
  calc Real.exp (Real.log M₀ + d * Real.log y + (Δα * lw' + Δβ * (u' - lw') + |Δα| + |Δβ|)) ≤ Real.exp (Real.log δ) :=
        Real.exp_le_exp.2 hlog
    _ = δ := Real.exp_log hδ

set_option maxHeartbeats 16000000 in
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
      ‖mellin H' ((x : ℂ) - 1)‖ ≤ δ * ‖mellin H (x : ℂ)‖ := by
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

  set A' : ℂ := κ - 1 - 1 - q' with hA'
  set B' : ℂ := p' - q' - 1 with hB'
  set τ' : ℝ := q'.im / 2 with hτ'
  set d : ℝ := (q'.re - q.re - 1) / 2 with hd
  set yof' : ℝ → ℝ := fun x => ((x - 1) + q'.re + 1) / 2 with hyof'
  set Sof' : ℝ → ℂ := fun x => ((((x - 1 : ℝ)) : ℂ) + q' + 1) / 2 with hSof'
  have hS'_eq : ∀ x : ℝ, Sof' x = ((yof' x : ℝ) : ℂ) + ((τ' : ℝ) : ℂ) * Complex.I := by
    intro x; simp only [hSof', hyof', hτ']; apply Complex.ext <;> simp <;> ring
  have hyy' : ∀ x : ℝ, yof' x = yof x + d := by intro x; simp only [hyof', hyof, hd]; ring
  set G' : ℝ → ℝ → ℝ → ℂ := fun y w r =>
      ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(((y : ℝ) : ℂ) + ((τ' : ℝ) : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A' * ((r : ℝ) : ℂ) ^ B' *
        (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) with hG'
  set T' : ℝ → ℝ → ℝ → ℝ := fun y w r => (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ A'.re * r ^ B'.re *
      Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) with hT'
  have hnormG' : ∀ (y w r : ℝ), 0 < w → 0 < r → ‖G' y w r‖ = T' y w r := by
    intro y w r hw hr
    have hv : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
    simp only [hG', hT']
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hw,
      Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    congr 2
    simp
  set cof' : ℝ → ℂ := fun x => 2 * C' * ((|a| : ℝ) : ℂ) ^ (1 + q') * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-Sof' x) * Complex.Gamma (Sof' x) with hcof'
  have hJF' : ∀ x : ℝ, |q'.re| + |p'.re| + 2 ≤ x →
      mellin H' ((x : ℂ) - 1) = cof' x * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G' (yof' x) w r ∧
      Integrable (fun v : ℝ × ℝ => G' (yof' x) v.1 v.2)
        (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    intro x hx
    have hzq : -1 < ((((x - 1 : ℝ)) : ℂ) + q').re := by simp; have := neg_abs_le q'.re; have := abs_nonneg p'.re; linarith
    have hzp : -1 < ((((x - 1 : ℝ)) : ℂ) + p').re := by simp; have := neg_abs_le p'.re; have := abs_nonneg q'.re; linarith
    obtain ⟨-, hI, hM⟩ := LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
      a ha p' q' (κ - 1) C' H' hH' (((x - 1 : ℝ)) : ℂ) hzq hzp
    have hexp : -((((x - 1 : ℝ) : ℂ) + q' + 1) / 2) = -(((yof' x : ℝ) : ℂ) + ((τ' : ℝ) : ℂ) * Complex.I) := by
      rw [← hS'_eq x]
    have hcast : (((x - 1 : ℝ)) : ℂ) = (x : ℂ) - 1 := by push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [← hcast, hM]; simp only [hcof', hSof', hG', hA', hB', hexp]
    · simpa only [hG', hA', hB', hexp] using hI

  obtain ⟨R₁, hR₁⟩ := LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral a ha A B τ (1/2) one_half_pos
  obtain ⟨R₂, hR₂⟩ := LanglandsTunnell.exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel a ha A'.re B'.re (1/2) 1 one_half_pos one_pos
  obtain ⟨Kg, Rg, hKg, hRg⟩ := LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma d τ τ'

  set Δα : ℝ := A'.re - A.re with hΔα
  set Δβ : ℝ := B'.re - B.re with hΔβ
  have hΔα_eq : Δα = -1 - q'.re + q.re := by simp only [hΔα, hA', hA, Complex.sub_re, Complex.one_re]; ring
  have hΔβ_eq : Δβ = p'.re - q'.re - p.re + q.re := by simp only [hΔβ, hB', hB, Complex.sub_re, Complex.one_re]; ring
  have hpq : p'.re + q'.re ≤ p.re + q.re := by simpa [Complex.add_re] using hpq'
  have hkey : d + (Δα + Δβ) / 6 ≤ -(2/3 : ℝ) := by rw [hd, hΔα_eq, hΔβ_eq]; linarith

  set ustar : ℝ → ℝ := fun y => (1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) with hustar
  set lw : ℝ → ℝ := fun y => (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ustar y)) / a ^ 2) with hlw
  set lr : ℝ → ℝ := fun y => ustar y - lw y with hlr

  have hCn : 0 < ‖C‖ := norm_pos_iff.mpr hC
  set L : ℝ := ‖C'‖ / ‖C‖ * |a| ^ (q'.re - q.re) * (Real.pi * a ^ 2) ^ (-d) * Kg with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  set M₀ : ℝ := 4 * (L + 1) * (2:ℝ) ^ |d| with hM₀
  have hM₀0 : 0 < M₀ := by rw [hM₀]; positivity
  set C₂ : ℝ := |Δα - Δβ| * ((abs (Real.log |a|)) / 2 + Real.log 2 / 4) + |Δα| + |Δβ|
      + |Δα + Δβ| / 6 * ((abs (Real.log (Real.pi * |a|))) + Real.log 2) with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  set Y₂ : ℝ := Real.exp ((3/2 : ℝ) * (Real.log M₀ + C₂ - Real.log δ)) with hY₂

  set Rm : ℝ := max 0 (max R₁ (max R₂ Rg)) with hRm
  have hRm0 : 0 ≤ Rm := le_max_left _ _
  set X₀ : ℝ := |q.re| + |p.re| + |q'.re| + |p'.re| + 2 * Rm + 4 * |d| + 2 * Real.pi * |a| * Real.exp 6 + 2 * Y₂ + 4 with hX₀
  refine ⟨X₀, fun x hx => ?_⟩
  have hqa : 0 ≤ |q.re| := abs_nonneg _
  have hpa' : 0 ≤ |p.re| := abs_nonneg _
  have hqa2 : 0 ≤ |q'.re| := abs_nonneg _
  have hpa2 : 0 ≤ |p'.re| := abs_nonneg _
  have hdabs : 0 ≤ |d| := abs_nonneg _
  have hY₂0 : 0 < Y₂ := by rw [hY₂]; exact Real.exp_pos _
  have hE6 : 0 < Real.pi * |a| * Real.exp 6 := by positivity
  rw [hX₀] at hx
  have hx0 : |q.re| + |p.re| + 1 ≤ x := by linarith
  have hx0' : |q'.re| + |p'.re| + 2 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  set y : ℝ := yof x with hy
  set y' : ℝ := yof' x with hy'
  have hyx : y = (x + q.re + 1) / 2 := rfl
  have hy'd : y' = y + d := hyy' x
  have hqre : -|q.re| ≤ q.re := neg_abs_le _
  have hdle : -|d| ≤ d := neg_abs_le _
  have hdle' : d ≤ |d| := le_abs_self _
  have hyRm : Rm + 2 * |d| + Real.pi * |a| * Real.exp 6 + Y₂ + 1 ≤ y := by rw [hyx]; linarith
  have hyR₁ : R₁ ≤ y := by have := (le_max_left R₁ (max R₂ Rg)).trans (le_max_right 0 _); linarith
  have hyRg : Rg ≤ y := by have := ((le_max_right R₂ Rg).trans (le_max_right R₁ _)).trans (le_max_right 0 _); linarith
  have hy'R₂ : R₂ ≤ y' := by have := ((le_max_left R₂ Rg).trans (le_max_right R₁ _)).trans (le_max_right 0 _); rw [hy'd]; linarith
  have hy1 : 1 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hy'big : Real.pi * |a| * Real.exp 6 ≤ y' := by rw [hy'd]; linarith
  have hy'pos : 0 < y' := hE6.trans_le hy'big
  have hy'lo : y / 2 ≤ y' := by rw [hy'd]; linarith
  have hy'hi : y' ≤ 2 * y := by rw [hy'd]; linarith
  have hyY₂ : Y₂ ≤ y := by linarith

  have hu'2 : 2 ≤ ustar y' := by
    simp only [hustar]
    have h1 : Real.exp 6 ≤ y' / (Real.pi * |a|) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := Real.log_le_log (Real.exp_pos 6) h1
    rw [Real.log_exp] at h2; linarith
  have hu'0 : 0 ≤ ustar y' := by linarith
  have hθ' : Real.exp (4 - 2 * ustar y') ≤ 1 := by rw [Real.exp_le_one_iff]; linarith

  obtain ⟨hM0, hI0⟩ := hJF x hx0
  obtain ⟨hM', hI'⟩ := hJF' x hx0'

  set μp : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμp
  set μ2 : Measure (ℝ × ℝ) := μp.prod μp with hμ2
  set F0 : ℝ × ℝ → ℂ := fun v => G y v.1 v.2 with hF0
  set F' : ℝ × ℝ → ℂ := fun v => G' y' v.1 v.2 with hF'
  have hI0' : Integrable F0 μ2 := hI0
  have hI'' : Integrable F' μ2 := hI'
  have hII0 : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G y w r) = ∫ v, F0 v ∂μ2 := by rw [hμ2, integral_prod _ hI0']
  have hII' : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G' y' w r) = ∫ v, F' v ∂μ2 := by rw [hμ2, integral_prod _ hI'']
  have hNN : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G y w r‖) = ∫ v, ‖F0 v‖ ∂μ2 := by rw [hμ2, integral_prod _ hI0'.norm]
  set N : ℝ := ∫ v, ‖F0 v‖ ∂μ2 with hN
  set N' : ℝ := ∫ v, ‖F' v‖ ∂μ2 with hN'
  have hN0 : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  have hN'0 : 0 ≤ N' := integral_nonneg (fun _ => norm_nonneg _)

  have hcoh : (1 - 1/2) * N ≤ ‖∫ v, F0 v ∂μ2‖ := by
    have h := hR₁ y hyR₁
    rw [hNN, hII0] at h
    exact h
  have hNle : N ≤ 2 * ‖∫ v, F0 v ∂μ2‖ := by linarith

  set Bw : Set ℝ := Icc (Real.exp (lw y' - 1)) (Real.exp (lw y' + 1)) with hBw
  set Br : Set ℝ := Icc (Real.exp (lr y' - 1)) (Real.exp (lr y' + 1)) with hBr
  have hBw_sub : Bw ⊆ Ioi 0 := fun w hw => (Real.exp_pos _).trans_le hw.1
  have hBr_sub : Br ⊆ Ioi 0 := fun r hr => (Real.exp_pos _).trans_le hr.1
  set Sb : Set (ℝ × ℝ) := Bw ×ˢ Br with hSb
  have hSm : MeasurableSet Sb := measurableSet_Icc.prod measurableSet_Icc
  have hrestr : μ2.restrict Sb = (volume.restrict Bw).prod (volume.restrict Br) := by
    rw [hμ2, hμp, hSb, ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hBw_sub, inter_eq_left.mpr hBr_sub]

  have hconc' : (1 - 1/2) * N' ≤ ∫ v in Sb, ‖F' v‖ ∂μ2 := by
    have h := hR₂ y' hy'R₂
    have hl : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T' y' w r) = N' := by
      have e : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T' y' w r) = ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G' y' w r‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_))
        exact (hnormG' y' w r hw hr).symm
      rw [e, hN', hμ2, integral_prod _ hI''.norm]
    have hr' : (∫ w in Bw, ∫ r in Br, T' y' w r) = ∫ v in Sb, ‖F' v‖ ∂μ2 := by
      rw [hrestr, integral_prod _ (hI''.norm.mono_measure (by rw [← hrestr]; exact Measure.restrict_le_self))]
      refine setIntegral_congr_fun measurableSet_Icc (fun w hw => setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_))
      exact (hnormG' y' w r (hBw_sub hw) (hBr_sub hr)).symm
    have h'' : (1 - 1/2) * (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T' y' w r) ≤ ∫ w in Bw, ∫ r in Br, T' y' w r := by
      simpa only [hT', hBw, hBr, hlw, hlr, hustar] using h
    rwa [hl, hr'] at h''

  set E : ℝ := Δα * lw y' + Δβ * lr y' + |Δα| + |Δβ| with hE
  have hbox : ∀ v : ℝ × ℝ, v ∈ Sb → ‖F' v‖ ≤ (2:ℝ) ^ |y - y'| * Real.exp E * ‖F0 v‖ := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    have hw0 : 0 < w := hBw_sub hw
    have hr0 : 0 < r := hBr_sub hr
    show ‖G' y' w r‖ ≤ (2:ℝ) ^ |y - y'| * Real.exp E * ‖G y w r‖
    rw [hnormG' y' w r hw0 hr0, hnormG y w r hw0 hr0]
    have h := LanglandsTunnell.tiltKernel_le_mul_tiltKernel_of_mem_logBox a ha y y' A.re B.re A'.re B'.re hypos.le hy'pos.le
      (by simpa only [hustar] using hθ') w r (by simpa only [hBw, hlw, hustar] using hw) (by simpa only [hBr, hlr, hlw, hustar] using hr)
    simpa only [hT', hT, hE, hΔα, hΔβ, hlw, hlr, hustar] using h
  have hbox_int : ∫ v in Sb, ‖F' v‖ ∂μ2 ≤ (2:ℝ) ^ |y - y'| * Real.exp E * N := by
    have h1 : ∫ v in Sb, ‖F' v‖ ∂μ2 ≤ ∫ v in Sb, (2:ℝ) ^ |y - y'| * Real.exp E * ‖F0 v‖ ∂μ2 :=
      setIntegral_mono_on hI''.norm.integrableOn (hI0'.norm.const_mul _).integrableOn hSm hbox
    rw [integral_const_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hN]; exact setIntegral_le_integral hI0'.norm (ae_of_all _ (fun _ => norm_nonneg _))
  have hdyy : |y - y'| = |d| := by rw [hy'd]; rw [show y - (y + d) = -d by ring, abs_neg]
  have hJ'le : ‖∫ v, F' v ∂μ2‖ ≤ 4 * (2:ℝ) ^ |d| * Real.exp E * ‖∫ v, F0 v ∂μ2‖ := by
    have h1 : ‖∫ v, F' v ∂μ2‖ ≤ N' := norm_integral_le_integral_norm _
    rw [hdyy] at hbox_int
    have h2 : N' ≤ 2 * ((2:ℝ) ^ |d| * Real.exp E * N) := by linarith
    calc ‖∫ v, F' v ∂μ2‖ ≤ N' := h1
      _ ≤ 2 * ((2:ℝ) ^ |d| * Real.exp E * N) := h2
      _ ≤ 2 * ((2:ℝ) ^ |d| * Real.exp E * (2 * ‖∫ v, F0 v ∂μ2‖)) := by gcongr
      _ = _ := by ring

  have hS_eq' : Sof x = ((y:ℝ):ℂ) + ((τ:ℝ):ℂ) * Complex.I := hS_eq x
  have hS'_eq' : Sof' x = (((y + d : ℝ)) : ℂ) + ((τ':ℝ):ℂ) * Complex.I := by rw [hS'_eq x, ← hy'd]
  have hΓ : ‖Complex.Gamma (Sof' x)‖ ≤ Kg * y ^ d * ‖Complex.Gamma (Sof x)‖ := by
    rw [hS'_eq', hS_eq']; exact hRg y hyRg
  have hcof_norm : ‖cof x‖ = 2 * ‖C‖ * |a| ^ (1 + q.re) * (Real.pi * a ^ 2) ^ (-y) * ‖Complex.Gamma (Sof x)‖ := by
    simp only [hcof]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha0,
      Complex.norm_cpow_eq_rpow_re_of_pos hpa, Complex.norm_two]
    have h1 : (1 + q).re = 1 + q.re := by simp
    have h2 : (-Sof x).re = -y := by rw [hS_eq']; simp
    rw [h1, h2]
  have hcof'_norm : ‖cof' x‖ = 2 * ‖C'‖ * |a| ^ (1 + q'.re) * (Real.pi * a ^ 2) ^ (-(y + d)) * ‖Complex.Gamma (Sof' x)‖ := by
    simp only [hcof']
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha0,
      Complex.norm_cpow_eq_rpow_re_of_pos hpa, Complex.norm_two]
    have h1 : (1 + q').re = 1 + q'.re := by simp
    have h2 : (-Sof' x).re = -(y + d) := by rw [hS'_eq']; simp
    rw [h1, h2]
  have hcof_le : ‖cof' x‖ ≤ L * y ^ d * ‖cof x‖ := by
    rw [hcof'_norm, hcof_norm, hL]
    have e1 : |a| ^ (1 + q'.re) = |a| ^ (q'.re - q.re) * |a| ^ (1 + q.re) := by
      rw [← Real.rpow_add ha0]; congr 1; ring
    have e2 : (Real.pi * a ^ 2) ^ (-(y + d)) = (Real.pi * a ^ 2) ^ (-d) * (Real.pi * a ^ 2) ^ (-y) := by
      rw [← Real.rpow_add hpa]; congr 1; ring
    rw [e1, e2]
    have hfac : 0 ≤ 2 * ‖C'‖ * (|a| ^ (q'.re - q.re) * |a| ^ (1 + q.re)) * ((Real.pi * a ^ 2) ^ (-d) * (Real.pi * a ^ 2) ^ (-y)) := by
      positivity
    calc 2 * ‖C'‖ * (|a| ^ (q'.re - q.re) * |a| ^ (1 + q.re)) * ((Real.pi * a ^ 2) ^ (-d) * (Real.pi * a ^ 2) ^ (-y)) *
          ‖Complex.Gamma (Sof' x)‖
        ≤ 2 * ‖C'‖ * (|a| ^ (q'.re - q.re) * |a| ^ (1 + q.re)) * ((Real.pi * a ^ 2) ^ (-d) * (Real.pi * a ^ 2) ^ (-y)) *
          (Kg * y ^ d * ‖Complex.Gamma (Sof x)‖) := mul_le_mul_of_nonneg_left hΓ hfac
      _ = ‖C'‖ / ‖C‖ * |a| ^ (q'.re - q.re) * (Real.pi * a ^ 2) ^ (-d) * Kg * y ^ d *
          (2 * ‖C‖ * |a| ^ (1 + q.re) * (Real.pi * a ^ 2) ^ (-y) * ‖Complex.Gamma (Sof x)‖) := by
          field_simp

  have hu'eq : ustar y' = (1/3 : ℝ) * (Real.log y' - Real.log (Real.pi * |a|)) := by
    simp only [hustar]; rw [Real.log_div hy'pos.ne' (by positivity)]
  have hla2 : Real.log (a ^ 2) = 2 * Real.log |a| := by rw [← sq_abs, Real.log_pow]; push_cast; ring
  have hlw_lo : ustar y' / 2 - Real.log |a| / 2 ≤ lw y' := by
    simp only [hlw]
    have h1 : Real.exp (2 * ustar y') / a ^ 2 ≤ (1 + Real.exp (2 * ustar y')) / a ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [Real.exp_pos (2 * ustar y')]) (by positivity)
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp, hla2] at h2
    linarith
  have hlw_hi : lw y' ≤ ustar y' / 2 - Real.log |a| / 2 + Real.log 2 / 4 := by
    simp only [hlw]
    have h0 : 1 ≤ Real.exp (2 * ustar y') := Real.one_le_exp (by linarith)
    have h1 : (1 + Real.exp (2 * ustar y')) / a ^ 2 ≤ 2 * Real.exp (2 * ustar y') / a ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, hla2] at h2
    rw [Real.log_div (by positivity) (by positivity), hla2]
    linarith
  have hbook := LanglandsTunnell.halfStep_logBook d Δα Δβ (Real.log |a|) (Real.log (Real.pi * |a|)) M₀ δ y y' (ustar y') (lw y')
    hM₀0 hδ hy1 hy'pos hy'lo hy'hi hkey hu'eq hlw_lo hlw_hi hyY₂
  have hE' : E = Δα * lw y' + Δβ * (ustar y' - lw y') + |Δα| + |Δβ| := by simp only [hE, hlr]

  rw [hM', hM0, hII', hII0, norm_mul (cof' x), norm_mul (cof x)]
  have hcofn : 0 ≤ ‖cof x‖ := norm_nonneg _
  have hI0n : 0 ≤ ‖∫ v, F0 v ∂μ2‖ := norm_nonneg _
  have hyd : 0 ≤ y ^ d := Real.rpow_nonneg hypos.le _
  have hL1 : L ≤ L + 1 := by linarith
  calc ‖cof' x‖ * ‖∫ v, F' v ∂μ2‖
      ≤ (L * y ^ d * ‖cof x‖) * (4 * (2:ℝ) ^ |d| * Real.exp E * ‖∫ v, F0 v ∂μ2‖) :=
        mul_le_mul hcof_le hJ'le (norm_nonneg _) (by positivity)
    _ = (4 * L * (2:ℝ) ^ |d|) * y ^ d * Real.exp E * (‖cof x‖ * ‖∫ v, F0 v ∂μ2‖) := by ring
    _ ≤ M₀ * y ^ d * Real.exp E * (‖cof x‖ * ‖∫ v, F0 v ∂μ2‖) := by
        gcongr
        rw [hM₀]; nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) |d|, hL0]
    _ ≤ δ * (‖cof x‖ * ‖∫ v, F0 v ∂μ2‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hcofn hI0n)
        rw [hE']; exact hbook

end S_LanglandsTunnell_norm_mellin_gaussTorusTransform_halfStep_le
end P2MW
export P2MW.S_LanglandsTunnell_norm_mellin_gaussTorusTransform_halfStep_le (solution)
