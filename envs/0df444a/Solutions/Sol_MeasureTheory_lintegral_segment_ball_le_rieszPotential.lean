-- Prove2me | solution 1 for MeasureTheory.lintegral_segment_ball_le_rieszPotential
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:10:16.673005+00:00
-- url     : https://prove2.me/submissions/d26e18bd-d9ff-450e-a58f-77d16db935e0

import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_MeasureTheory_lintegral_mul_segment_eq_dilation_adjoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set Metric
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.segment_ball_rayKernel_bound {n : ℕ} (hn : 0 < n)
    (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    (∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((t ^ n)⁻¹) *
        (if t⁻¹ * ρ < r then ENNReal.ofReal (t⁻¹ * ρ) else 0)) ≤
      ENNReal.ofReal (r ^ n / (n : ℝ) * ρ ^ (1 - (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < ρ / r := div_pos hρ hr
  have he : -(n : ℝ) - 1 < -1 := by linarith
  calc
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (Ioi (ρ / r)).indicator
        (fun t => ENNReal.ofReal (ρ * t ^ (-(n : ℝ) - 1))) t := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      by_cases htr : t⁻¹ * ρ < r
      · have hat : ρ / r < t := by
          rw [div_lt_iff₀ hr]
          have := (inv_mul_lt_iff₀ ht.1).mp htr
          nlinarith
        rw [if_pos htr, indicator_of_mem (show t ∈ Ioi (ρ / r) from hat),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ht.1.le _))]
        apply le_of_eq
        congr 1
        rw [Real.rpow_sub ht.1, Real.rpow_neg ht.1.le, Real.rpow_natCast,
          Real.rpow_one]
        field_simp
      · simp [htr]
    _ ≤ ∫⁻ t, (Ioi (ρ / r)).indicator
        (fun t => ENNReal.ofReal (ρ * t ^ (-(n : ℝ) - 1))) t :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = ENNReal.ofReal (ρ * (- (ρ / r) ^ (-(n : ℝ) - 1 + 1) /
        (-(n : ℝ) - 1 + 1))) := by
      rw [lintegral_indicator measurableSet_Ioi,
        ← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_Ioi_rpow_of_lt he ha).const_mul ρ)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg hρ.le (Real.rpow_nonneg (ha.trans ht).le _)),
        integral_const_mul, integral_Ioi_rpow_of_lt he ha]
    _ = _ := by
      congr 1
      rw [show -(n : ℝ) - 1 + 1 = -(n : ℝ) by ring,
        Real.rpow_neg ha.le, Real.div_rpow hρ.le hr.le, Real.rpow_natCast,
        Real.rpow_sub hρ, Real.rpow_one, Real.rpow_natCast]
      field_simp
      exact (Real.rpow_natCast ρ n)


theorem solution {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ENNReal,
      Measurable g → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖z - x‖ *
        (∫⁻ t in Set.Icc (0 : ℝ) 1, g (x + t • (z - x)))) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, g z *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let V : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV : 0 < V := by
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne'
      (measure_ball_lt_top.ne)
  refine ⟨(1 / ((n : ℝ) * V)).toNNReal, fun g hg x r hr => ?_⟩
  let f : EuclideanSpace ℝ (Fin n) → ENNReal :=
    (ball 0 r).indicator (fun y => g (x + y))
  let h : EuclideanSpace ℝ (Fin n) → ENNReal :=
    (ball 0 r).indicator (fun y => ENNReal.ofReal ‖y‖)
  have hf : Measurable f := (hg.comp (measurable_const.add measurable_id)).indicator
    measurableSet_ball
  have hh : Measurable h := measurable_id.norm.ennreal_ofReal.indicator measurableSet_ball
  have hadj := MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint volume f h hf hh
  have hleft : (∫⁻ z in ball x r, ENNReal.ofReal ‖z - x‖ *
      (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (z - x)))) =
      ∫⁻ z, h z * (∫⁻ t in Icc (0 : ℝ) 1, f (t • z)) := by
    have ht := (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.addLeft x).measurableEmbedding
      (fun z => ENNReal.ofReal ‖z - x‖ *
        (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (z - x)))) (ball x r)
    have hs : (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' ball x r = ball 0 r := by
      ext y
      simp [mem_ball, dist_eq_norm]
    rw [hs] at ht
    rw [← ht, ← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ ball 0 r
    · simp only [indicator_of_mem hz, h, add_sub_cancel_left]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      have htz : t • z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        have hz' : ‖z‖ < r := mem_ball_zero_iff.mp hz
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz'
      simp [f, htz]
    · simp [h, hz]
  have hright : (∫⁻ y, f y * (∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((t ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) * h (t⁻¹ • y))) ≤
      ENNReal.ofReal (r ^ n / (n : ℝ)) *
        (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) r,
          g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) := by
    have hm : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) :=
      (hg.comp (measurable_const.add measurable_id)).mul
        ((measurable_id.norm.pow_const _).ennreal_ofReal)
    rw [← lintegral_const_mul _ hm,
      ← lintegral_indicator measurableSet_ball]
    apply lintegral_mono_ae
    have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin n), y ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hzero] with y hy0
    by_cases hyr : y ∈ ball 0 r
    · simp only [f, indicator_of_mem hyr]
      have hk := MeasureTheory.segment_ball_rayKernel_bound hn r ‖y‖ hr (norm_pos_iff.mpr hy0)
      have heq : (∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((t ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) * h (t⁻¹ • y)) =
          ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((t ^ n)⁻¹) *
            (if t⁻¹ * ‖y‖ < r then ENNReal.ofReal (t⁻¹ * ‖y‖) else 0) := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only
        have hnorm : ‖t⁻¹ • y‖ = t⁻¹ * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht.1)]
        by_cases htmem : t⁻¹ • y ∈ ball 0 r
        · rw [show h (t⁻¹ • y) = ENNReal.ofReal ‖t⁻¹ • y‖ from
            indicator_of_mem htmem _, hnorm, if_pos (by simpa [mem_ball_zero_iff, hnorm] using htmem)]
          simp
        · rw [show h (t⁻¹ • y) = 0 from indicator_of_notMem htmem _,
            if_neg (by simpa [mem_ball_zero_iff, hnorm] using htmem)]
          simp
      rw [heq]
      calc
        _ ≤ g (x + y) * ENNReal.ofReal (r ^ n / (n : ℝ) * ‖y‖ ^ (1 - (n : ℝ))) :=
          mul_le_mul (le_refl _) hk (by positivity) (by positivity)
        _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ac_rfl
    · simp [f, hyr]
  have hvol : volume (ball x r) *
      (((1 / ((n : ℝ) * V)).toNNReal : NNReal) : ENNReal) =
      ENNReal.ofReal (r ^ n / (n : ℝ)) := by
    rw [Measure.addHaar_ball volume x hr.le]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [← ENNReal.ofReal_toReal (measure_ball_lt_top.ne)]
    change ENNReal.ofReal (r ^ n) * ENNReal.ofReal V *
      ENNReal.ofReal (1 / ((n : ℝ) * V)) = _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have htrans : (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) r,
      g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) =
      ∫⁻ z in ball x r, g z * ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) := by
    have ht := (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.addLeft x).measurableEmbedding
      (fun z => g z * ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) (ball x r)
    have hs : (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' ball x r = ball 0 r := by
      ext y
      simp [mem_ball, dist_eq_norm]
    simpa [hs, add_sub_cancel_left] using ht
  rw [hleft, hadj, hvol]
  exact hright.trans_eq (congrArg (ENNReal.ofReal (r ^ n / (n : ℝ)) * ·) htrans)
