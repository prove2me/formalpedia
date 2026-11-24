-- Prove2me | solution 1 for Kyprianou.Ch03.stableExpAbsoluteDeficitBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:47:26.871074+00:00
-- url     : https://prove2.me/submissions/26186206-f2c1-4378-8746-3bd85bfdbeeb

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hne : ¬ Y =ᵐ[P] 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (∫ w, Real.exp (-s * |Y w|) ∂P) ≤ Real.exp (-c * s) := by
  have hi (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun w => Real.exp (-s * |Y w|)) P := by
    apply (integrable_const (1 : ℝ)).mono
    · exact (Real.continuous_exp.measurable.comp_aemeasurable
        (aemeasurable_const.mul hY.abs)).aestronglyMeasurable
    · filter_upwards with w
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (abs_nonneg _))
  have hi1 := hi 1 (by norm_num)
  let f : Ω → ℝ := fun w => 1 - Real.exp (-1 * |Y w|)
  have hf : Integrable f P := (integrable_const 1).sub hi1
  have hfnon : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall fun w => by
    dsimp [f]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg _)))
  let c := ∫ w, f w ∂P
  have hc : 0 < c := by
    have h0 : 0 ≤ c := integral_nonneg_of_ae hfnon
    apply lt_of_le_of_ne h0
    intro he
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hfnon hf).mp he.symm
    apply hne
    filter_upwards [hzero] with w hw
    change 1 - Real.exp (-1 * |Y w|) = 0 at hw
    have hh : Real.exp (-1 * |Y w|) = Real.exp 0 := by
      rw [Real.exp_zero]; linarith
    have hz := Real.exp_injective hh
    change Y w = 0
    exact abs_eq_zero.mp (by linarith)
  refine ⟨c, hc, fun s hs hs1 => ?_⟩
  have hbound : (∫ w, Real.exp (-s * |Y w|) ∂P) ≤
      ∫ w, (1 - s * f w) ∂P := by
    apply integral_mono_ae (hi s hs) ((integrable_const 1).sub (hf.const_mul s))
    filter_upwards with w
    have hh := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-|Y w|))
      (show 0 ≤ 1 - s by linarith) hs (by ring)
    simp only [smul_eq_mul, Real.exp_zero, mul_zero, zero_add, mul_one] at hh
    rw [show s * (-|Y w|) = -s * |Y w| by ring] at hh
    dsimp [f]
    rw [neg_one_mul]
    linarith
  rw [integral_sub (integrable_const 1) (hf.const_mul s), integral_const_mul] at hbound
  simp [integral_const, Measure.real] at hbound
  have hE : 1 - s * c ≤ Real.exp (-c * s) := by
    nlinarith only [Real.add_one_le_exp (-c * s)]
  simpa only [neg_mul] using hbound.trans hE
