-- Prove2me | solution 1 for MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/73942432-afdb-5eba-b1c7-3c56a7dcc274

import Definitions.Def_MvPolynomial_LogMahlerMeasure
import Theorems.Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv

open MeasureTheory Real

namespace MvPolynomial
p2m_export "MvPolynomial" "degreeOf map coeff funext finSuccEquiv natDegree_finSuccEquiv eval_eq_eval_mv_eval' ext eval coeff_map torusBox volume_restrict_torusBox logMahlerMeasure logMahlerMeasure_def integrableOn_log_norm_eval_circleMap"
p2m_open "MvPolynomial"

variable {n : ℕ}

noncomputable abbrev circleParamMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))

noncomputable abbrev torusMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n ↦ circleParamMeasure

scoped instance : IsFiniteMeasure (circleParamMeasure) := by
  unfold circleParamMeasure; infer_instance

scoped instance : IsFiniteMeasure (torusMeasure n) := by
  unfold torusMeasure; infer_instance

theorem circleParamMeasure_univ : circleParamMeasure Set.univ = ENNReal.ofReal (2 * π) := by
  simp [Real.volume_Ioc]

theorem torusMeasure_univ : torusMeasure n Set.univ = ENNReal.ofReal (2 * π) ^ n := by
  rw [torusMeasure, Measure.pi_univ]
  simp

theorem torusMeasure_real_univ : (torusMeasure n).real Set.univ = (2 * π) ^ n := by
  simp [Measure.real, torusMeasure_univ, ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.pi_pos.le]

theorem logMahlerMeasure_eq_mul_integral_torusMeasure (P : MvPolynomial (Fin n) ℂ) :
    P.logMahlerMeasure =
      ((2 * π)⁻¹) ^ n * ∫ θ, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ∂(torusMeasure n) := by
  rw [logMahlerMeasure, volume_restrict_torusBox]

noncomputable def torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ) (θ' : Fin n → ℝ) : Polynomial ℂ :=
  Polynomial.map (eval (fun i ↦ circleMap 0 1 (θ' i))) (finSuccEquiv ℂ n P)

theorem eval_circleMap_cons (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℝ) (θ' : Fin n → ℝ) :
    eval (fun i ↦ circleMap 0 1 ((Fin.cons x θ' : Fin (n + 1) → ℝ) i)) P =
      (torusFiber P θ').eval (circleMap 0 1 x) := by
  have : (fun i ↦ circleMap 0 1 ((Fin.cons x θ' : Fin (n + 1) → ℝ) i)) =
      Fin.cons (circleMap 0 1 x) (fun i ↦ circleMap 0 1 (θ' i)) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [this, eval_eq_eval_mv_eval']
  rfl

theorem coeff_torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ) (θ' : Fin n → ℝ) (k : ℕ) :
    (torusFiber P θ').coeff k = eval (fun i ↦ circleMap 0 1 (θ' i)) ((finSuccEquiv ℂ n P).coeff k) := by
  simp [torusFiber, Polynomial.coeff_map]

theorem natDegree_torusFiber_le (P : MvPolynomial (Fin (n + 1)) ℂ) (θ' : Fin n → ℝ) :
    (torusFiber P θ').natDegree ≤ P.degreeOf 0 :=
  Polynomial.natDegree_map_le.trans (natDegree_finSuccEquiv P).le

noncomputable abbrev torusSplit (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0

theorem torusSplit_symm_apply (z : ℝ × (Fin n → ℝ)) :
    (torusSplit n).symm z = Fin.cons z.1 z.2 := by
  funext j
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, Fin.insertNth_zero']

theorem measurePreserving_torusSplit (n : ℕ) :
    MeasurePreserving (torusSplit n) (torusMeasure (n + 1))
      (circleParamMeasure.prod (torusMeasure n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ circleParamMeasure) 0

theorem finSuccEquiv_ne_zero {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P ≠ 0) :
    finSuccEquiv ℂ n P ≠ 0 := by
  simpa using (finSuccEquiv ℂ n).injective.ne hP

theorem integrable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Integrable (fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖) (torusMeasure n) := by
  have h := integrableOn_log_norm_eval_circleMap P
  rw [IntegrableOn, volume_restrict_torusBox] at h
  exact h

private theorem _root_.Real.abs_log_eq_two_mul_posLog_sub_log (t : ℝ) : |Real.log t| = 2 * t.posLog - Real.log t := by
  rw [Real.posLog_def, Pi.sup_apply, Pi.zero_apply]
  rcases le_total 0 (Real.log t) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

p2m_alias "P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.Real.abs_log_eq_two_mul_posLog_sub_log" "Real.abs_log_eq_two_mul_posLog_sub_log"
private theorem _root_.Polynomial.integral_log_norm_eval_circleMap (p : Polynomial ℂ) :
    ∫ x in Set.Ioc 0 (2 * π), Real.log ‖p.eval (circleMap 0 1 x)‖ = (2 * π) * p.logMahlerMeasure := by
  rw [p.logMahlerMeasure_def, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le, ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul]

p2m_alias "P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.Polynomial.integral_log_norm_eval_circleMap" "Polynomial.integral_log_norm_eval_circleMap"
private theorem _root_.Polynomial.integrableOn_log_norm_eval_circleMap (p : Polynomial ℂ) :
    IntegrableOn (fun x ↦ Real.log ‖p.eval (circleMap 0 1 x)‖) (Set.Ioc 0 (2 * π)) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp p.intervalIntegrable_mahlerMeasure

p2m_alias "P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.Polynomial.integrableOn_log_norm_eval_circleMap" "Polynomial.integrableOn_log_norm_eval_circleMap"
theorem integrable_log_norm_eval_torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Integrable (fun z : ℝ × (Fin n → ℝ) ↦ Real.log ‖(torusFiber P z.2).eval (circleMap 0 1 z.1)‖)
      (circleParamMeasure.prod (torusMeasure n)) := by
  have hFG : (fun θ : Fin (n + 1) → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖) ∘
      (torusSplit n).symm =
      fun z : ℝ × (Fin n → ℝ) ↦ Real.log ‖(torusFiber P z.2).eval (circleMap 0 1 z.1)‖ := by
    funext z; simp [torusSplit_symm_apply, eval_circleMap_cons,
      -MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [← hFG, (measurePreserving_torusSplit n).symm.integrable_comp_emb
      (torusSplit n).symm.measurableEmbedding]
  exact integrable_log_norm_eval_circleMap P

theorem integrable_logMahlerMeasure_torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Integrable (fun θ' ↦ (torusFiber P θ').logMahlerMeasure) (torusMeasure n) := by
  have h := (integrable_log_norm_eval_torusFiber P).integral_prod_right
  have h2 : (fun θ' : Fin n → ℝ ↦ (torusFiber P θ').logMahlerMeasure) =
      fun θ' ↦ (2 * π)⁻¹ * ∫ x, Real.log ‖(torusFiber P θ').eval (circleMap 0 1 x)‖
        ∂circleParamMeasure := by
    funext θ'
    rw [show (∫ x, Real.log ‖(torusFiber P θ').eval (circleMap 0 1 x)‖ ∂circleParamMeasure) = _
      from (torusFiber P θ').integral_log_norm_eval_circleMap, ← mul_assoc,
      inv_mul_cancel₀ two_pi_pos.ne', one_mul]
  rw [h2]
  exact h.const_mul _

theorem integral_log_norm_eval_circleMap_succ (P : MvPolynomial (Fin (n + 1)) ℂ) :
    ∫ θ, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ∂(torusMeasure (n + 1)) =
      ∫ θ', (2 * π) * (torusFiber P θ').logMahlerMeasure ∂(torusMeasure n) := by
  calc ∫ θ, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ∂(torusMeasure (n + 1))
      = ∫ z, Real.log ‖eval (fun i ↦ circleMap 0 1 ((torusSplit n).symm z i)) P‖
          ∂(circleParamMeasure.prod (torusMeasure n)) :=
        ((measurePreserving_torusSplit n).symm.integral_comp (torusSplit n).symm.measurableEmbedding
          (fun θ : Fin (n + 1) → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖)).symm
    _ = ∫ z, Real.log ‖(torusFiber P z.2).eval (circleMap 0 1 z.1)‖
          ∂(circleParamMeasure.prod (torusMeasure n)) := by
        congr 1; funext z
        simp [torusSplit_symm_apply, eval_circleMap_cons, -MeasurableEquiv.piFinSuccAbove_symm_apply]
    _ = ∫ θ', ∫ x, Real.log ‖(torusFiber P θ').eval (circleMap 0 1 x)‖ ∂circleParamMeasure
          ∂(torusMeasure n) :=
        integral_prod_symm _ (integrable_log_norm_eval_torusFiber P)
    _ = _ := by
        congr 1; funext θ'
        exact (torusFiber P θ').integral_log_norm_eval_circleMap

theorem logMahlerMeasure_eq_mul_integral_logMahlerMeasure_torusFiber
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    P.logMahlerMeasure =
      ((2 * π)⁻¹) ^ n * ∫ θ', (torusFiber P θ').logMahlerMeasure ∂(torusMeasure n) := by
  rw [logMahlerMeasure_eq_mul_integral_torusMeasure, integral_log_norm_eval_circleMap_succ,
    integral_const_mul, pow_succ, mul_assoc, inv_mul_cancel_left₀ two_pi_pos.ne']

end MvPolynomial
p2m_reactivate "P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.MvPolynomial"

theorem solution {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    P.logMahlerMeasure = ((2 * Real.pi)⁻¹) ^ n *
      ∫ θ' in MvPolynomial.torusBox n,
        (Polynomial.map (MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ' i)))
          (MvPolynomial.finSuccEquiv ℂ n P)).logMahlerMeasure := by
  rw [MvPolynomial.volume_restrict_torusBox]
  exact MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_torusFiber P

end S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv
end P2MW
export P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv (solution)
