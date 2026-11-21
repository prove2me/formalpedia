-- Prove2me | solution 2 for MasulloRH.weighted_zero_summability
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:13:59.764113+00:00
-- url     : https://prove2.me/submissions/8f2a4c82-cef5-45e7-a746-c0087187434c

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff
open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) :
    Summable (zeroDecayWeight α) := by
  -- the proved summability over all critical-strip zeros
  have hC := ConnesRZ.actual_zero_reciprocal_square_summable
  -- inclusion of the strip zeros into the critical zeros
  let ι : ZetaZerosInTraceStrip α → {z : ℂ // ConnesRZ.IsCriticalZero z} :=
    fun ρ => ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1⟩
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [ι] using this
  have hsub := (hC.comp_injective hι).mul_left (5 / 4 : ℝ)
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hsub
  · unfold zeroDecayWeight
    positivity
  · obtain ⟨r, hz, hr0, hr1, hstrip⟩ := ρ
    simp only [zeroDecayWeight, Function.comp_apply, ι, ConnesRZ.zeroMult]
    set m : ℝ := (analyticOrderNatAt riemannZeta r : ℝ)
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hns : Complex.normSq ((r - 1 / 2) / Complex.I) = (r.re - 1 / 2) ^ 2 + r.im ^ 2 := by
      rw [Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_apply]
      simp
      ring
    rw [hns]
    have hb : (r.re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith
    have hd1 : 0 < 1 + r.im ^ 2 := by positivity
    have hd2 : 0 < 1 + ((r.re - 1 / 2) ^ 2 + r.im ^ 2) := by positivity
    rw [div_le_iff₀ hd1]
    rw [show 5 / 4 * (m / (1 + ((r.re - 1 / 2) ^ 2 + r.im ^ 2))) * (1 + r.im ^ 2)
        = m * (5 / 4 * (1 + r.im ^ 2)) / (1 + ((r.re - 1 / 2) ^ 2 + r.im ^ 2)) by ring]
    rw [le_div_iff₀ hd2]
    have : 1 + ((r.re - 1 / 2) ^ 2 + r.im ^ 2) ≤ 5 / 4 * (1 + r.im ^ 2) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hm
