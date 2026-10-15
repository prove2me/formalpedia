-- Prove2me | solution 1 for MeasureTheory.lintegral_mul_rieszKernel_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:17:39.337139+00:00
-- url     : https://prove2.me/submissions/0b7b03e5-7e8a-44ba-b8a8-dbb2754a5f9f

import Theorems.Thm_MeasureTheory_integral_norm_rpow_ball
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set Metric
set_option autoImplicit false

theorem solution {n : ℕ} {p : ℝ} (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable g volume →
      ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |g z| *
        ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) ≤
        (C : ENNReal) * eLpNorm g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x r)) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
  have hn1 : 1 ≤ n := hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hp1 : 1 < p := lt_of_le_of_lt hnR hnp
  have hp : 0 < p := by linarith
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq : 0 < q := hpq.symm.pos
  let α : ℝ := n + (1 - (n : ℝ)) * q
  have hαeq : α = (p - n) / (p - 1) := by
    dsimp [α, q]
    field_simp [hp.ne', (sub_pos.mpr hp1).ne']
    ring
  have hα : 0 < α := by rw [hαeq]; exact div_pos (sub_pos.mpr hnp) (sub_pos.mpr hp1)
  have hexp : α / q = 1 - (n : ℝ) / p := by
    rw [hαeq]
    dsimp [q]
    field_simp [hp.ne', (sub_pos.mpr hp1).ne']
  let K : ℝ := (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / α
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(K ^ (1 / q)).toNNReal, fun g hg x r hr => ?_⟩
  let μ := volume.restrict (ball x r)
  have hkmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) => ‖z - x‖ ^ (1 - (n : ℝ))) :=
    (continuous_id.sub continuous_const).norm.measurable.pow_const _
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hg.aemeasurable.norm.ennreal_ofReal.restrict)
    (hkmeas.ennreal_ofReal.aemeasurable)
  have hnorm : (∫⁻ z, ENNReal.ofReal |g z| ^ p ∂μ) ^ (1 / p) =
      eLpNorm g (ENNReal.ofReal p) μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top]
    simp [ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal_abs]
  have hrad := MeasureTheory.integral_norm_rpow_ball n hn1 α hα r hr
  have hzero : (∫⁻ z : EuclideanSpace ℝ (Fin n) in ball 0 r,
      ENNReal.ofReal (‖z‖ ^ (α - n))) = ENNReal.ofReal (K * r ^ α) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hrad.1
      (Filter.Eventually.of_forall (fun z => Real.rpow_nonneg (norm_nonneg z) _)), hrad.2]
    congr 1
    dsimp [K]
    ring
  have htrans : (∫⁻ z : EuclideanSpace ℝ (Fin n) in ball x r,
      ENNReal.ofReal (‖z - x‖ ^ (α - n))) = ENNReal.ofReal (K * r ^ α) := by
    have ht := (measurePreserving_sub_right volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.subRight x).measurableEmbedding
      (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖z‖ ^ (α - n))) (ball 0 r)
    have hs : (fun z : EuclideanSpace ℝ (Fin n) => z - x) ⁻¹' ball 0 r = ball x r := by
      ext z
      simp [mem_ball, dist_eq_norm]
    rw [hs] at ht
    exact ht.trans hzero
  have hpower : (∫⁻ z, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) ^ q ∂μ) =
      ENNReal.ofReal (K * r ^ α) := by
    rw [← htrans]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq.le,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    dsimp [α]
    ring
  have hscale : (ENNReal.ofReal (K * r ^ α)) ^ (1 / q) =
      ((K ^ (1 / q)).toNNReal : ENNReal) * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.rpow_nonneg hr.le _)) (by positivity),
      Real.mul_rpow hK (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      show α * (1 / q) = 1 - (n : ℝ) / p by simpa only [div_eq_mul_inv, one_mul] using hexp, ENNReal.ofReal_mul (Real.rpow_nonneg hK _)]
    rfl
  simp only [Real.norm_eq_abs] at hholder
  rw [hnorm, hpower, hscale] at hholder
  simpa only [Pi.mul_apply, μ, mul_comm, mul_left_comm, mul_assoc] using hholder



