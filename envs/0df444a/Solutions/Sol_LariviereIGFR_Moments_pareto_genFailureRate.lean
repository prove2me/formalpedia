-- Prove2me | solution 1 for LariviereIGFR.Moments.pareto_genFailureRate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:05:06.731618+00:00
-- url     : https://prove2.me/submissions/0c003db6-d8dd-4628-9e4d-96b3c21d850d

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LariviereIGFR.Moments

theorem solution (S k : ℝ) (hS : 0 < S) (hk : 0 < k) :
    ∀ ξ, S ≤ ξ → LariviereIGFR.Char.genFailureRate (paretoMeasure S k) (paretoPDFReal S k) ξ = k := by
  intro ξ hξ
  have hξpos : 0 < ξ := lt_of_lt_of_le hS hξ
  haveI : IsProbabilityMeasure (paretoMeasure S k) := isProbabilityMeasure_paretoMeasure hS hk
  have h1 : (paretoMeasure S k).real (Set.Ioi ξ) = ∫ x in Set.Ioi ξ, paretoPDFReal S k x := by
    rw [measureReal_def, paretoMeasure, withDensity_apply _ measurableSet_Ioi]
    refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
    · exact ae_of_all _ fun _ => by simp only [Pi.zero_apply, paretoPDFReal_nonneg hS.le hk.le]
    · exact (measurable_paretoPDFReal S k).aestronglyMeasurable.restrict
  have h2 : ∫ x in Set.Ioi ξ, paretoPDFReal S k x = ∫ x in Set.Ioi ξ, k * S ^ k * x ^ (-(k + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have : S ≤ x := hξ.trans (le_of_lt hx)
    simp [paretoPDFReal, this]
  have h3 : ∫ x in Set.Ioi ξ, k * S ^ k * x ^ (-(k + 1)) = S ^ k * ξ ^ (-k) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hξpos]
    have : -(k + 1) + 1 = -k := by ring
    rw [this]
    field_simp
  have hsurv : LariviereIGFR.Char.survival (paretoMeasure S k) ξ = S ^ k * ξ ^ (-k) := by
    have := probReal_compl_eq_one_sub (μ := paretoMeasure S k) (measurableSet_Iic (a := ξ))
    rw [Set.compl_Iic] at this
    unfold LariviereIGFR.Char.survival
    rw [cdf_eq_real, ← this, h1, h2, h3]
  unfold LariviereIGFR.Char.genFailureRate LariviereIGFR.Char.failureRate
  rw [hsurv]
  have hpdf : paretoPDFReal S k ξ = k * S ^ k * ξ ^ (-(k + 1)) := by
    simp [paretoPDFReal, hξ]
  rw [hpdf]
  have hSk : 0 < S ^ k := Real.rpow_pos_of_pos hS k
  have hξk : 0 < ξ ^ (-k) := Real.rpow_pos_of_pos hξpos _
  have : ξ ^ (-(k + 1)) = ξ ^ (-k) / ξ := by
    rw [neg_add, Real.rpow_add hξpos, Real.rpow_neg_one]
    field_simp
  rw [this]
  field_simp
