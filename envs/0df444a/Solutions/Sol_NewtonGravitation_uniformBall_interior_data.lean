-- Prove2me | solution 1 for NewtonGravitation.uniformBall_interior_data
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:09:59.710165+00:00
-- url     : https://prove2.me/submissions/09559822-35d7-4dca-b525-bcfccc743c99

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation Metric
open scoped Pointwise

namespace NGAux

lemma G_pos : 0 < G := by unfold G; norm_num

lemma finrank_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

lemma kern_meas : Measurable (fun z : Space => -(G / ‖z‖ ^ 3) • z) := by fun_prop

lemma kern_integrableOn_ball (ρ : ℝ) :
    IntegrableOn (fun z : Space => -(G / ‖z‖ ^ 3) • z) (ball 0 ρ) volume := by
  refine integrableOn_ball_of_norm_le_rpow (α := 2) (C := G) (by rw [finrank_space]; norm_num)
    (by rw [finrank_space]; norm_num) (Filter.Eventually.of_forall fun z => ?_)
    kern_meas.aestronglyMeasurable
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos G_pos (pow_pos hn 3)),
    Real.rpow_neg hn.le, Real.rpow_two]
  field_simp
  rfl

lemma kern_integrableOn_shift (x : Space) (R : ℝ) :
    IntegrableOn (fun y : Space => -(G / ‖x - y‖ ^ 3) • (x - y)) (ball 0 R) volume := by
  have h1 := (kern_integrableOn_ball (‖x‖ + R)).integrable_indicator measurableSet_ball
  have h2 := h1.comp_sub_left x
  refine (h2.integrableOn (s := ball 0 R)).congr_fun (fun y hy => ?_) measurableSet_ball
  have : x - y ∈ ball (0 : Space) (‖x‖ + R) := by
    rw [mem_ball_zero_iff] at hy ⊢
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ < _ := by linarith
  simp [Set.indicator_of_mem this]

lemma vol_ball_ne_zero (R : ℝ) (hR : 0 < R) : volume (ball (0 : Space) R) ≠ 0 :=
  (measure_ball_pos volume 0 hR).ne'

lemma ball_const_ne_top (M : NNReal) (R : ℝ) (hR : 0 < R) :
    ((M : ENNReal) / volume (ball (0 : Space) R)) ≠ ⊤ :=
  ENNReal.div_ne_top ENNReal.coe_ne_top (vol_ball_ne_zero R hR)

lemma uniformBall_isFinite (M : NNReal) (R : ℝ) (hR : 0 < R) :
    IsFiniteMeasure (uniformBall M R) := by
  constructor
  rw [uniformBall, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, smul_eq_mul]
  exact ENNReal.mul_lt_top (ball_const_ne_top M R hR).lt_top
    (measure_lt_top_of_subset Set.inter_subset_right measure_ball_lt_top.ne)

lemma uniformBall_symm (M : NNReal) (R : ℝ) : IsSphericallySymmetric (uniformBall M R) := by
  intro A
  rw [uniformBall, Measure.map_smul]
  congr 1
  have hpre : A ⁻¹' ball (0 : Space) R = ball 0 R := by ext y; simp
  have hA : MeasurePreserving A volume volume := A.measurePreserving
  conv_lhs => rw [← hpre]
  rw [← Measure.restrict_map A.continuous.measurable measurableSet_ball, hA.map_eq]

lemma uniformBall_real_ball (M : NNReal) (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) :
    (uniformBall M R).real (ball (0 : Space) r) = (M : ℝ) * (min r R / R) ^ 3 := by
  rw [uniformBall, measureReal_def, Measure.smul_apply, Measure.restrict_apply measurableSet_ball,
    smul_eq_mul]
  have hb : ball (0 : Space) r ∩ ball 0 R = ball 0 (min r R) := by
    ext y; simp
  rw [hb, Measure.addHaar_ball _ _ (le_min hr hR.le), Measure.addHaar_ball _ _ hR.le,
    finrank_space]
  have h1 : volume (ball (0 : Space) 1) ≠ 0 := vol_ball_ne_zero 1 one_pos
  have h2 : volume (ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have h3 : (volume (ball (0 : Space) 1)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h1, h2⟩
  simp only [ENNReal.coe_toReal]
  field_simp

end NGAux

open NGAux in
theorem solution (M : NNReal) (R : ℝ)
    (hR : 0 < R) (x : Space) (hx : ‖x‖ < R) :
    IsFiniteMeasure (uniformBall M R) ∧
      IsSphericallySymmetric (uniformBall M R) ∧
      Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) (uniformBall M R) ∧
      (uniformBall M R).real (Metric.ball (0 : Space) ‖x‖) =
        (M : ℝ) * (‖x‖ / R) ^ 3 := by
  refine ⟨uniformBall_isFinite M R hR, uniformBall_symm M R, ?_, ?_⟩
  · exact (kern_integrableOn_shift x R).smul_measure (ball_const_ne_top M R hR)
  · rw [uniformBall_real_ball M R hR _ (norm_nonneg x), min_eq_left hx.le]
