-- Prove2me | solution 1 for MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8b0074b9-8f62-5cb1-ae53-d879976426c0

import Definitions.Def_MvPolynomial_LogMahlerMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero

open MeasureTheory Real

namespace MvPolynomial
p2m_export "MvPolynomial" "degreeOf map coeff eq_C_of_isEmpty funext finSuccEquiv natDegree_finSuccEquiv eval_eq_eval_mv_eval' ext C eval coeff_map coeff_zero torusBox volume_restrict_torusBox logMahlerMeasure continuous_eval_circleMap"
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

private theorem _root_.Polynomial.finite_setOf_eval_circleMap_eq_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    ({x | p.eval (circleMap 0 1 x) = 0} ∩ Set.Ioc 0 (2 * π)).Finite := by
  apply Set.Finite.of_finite_image (f := circleMap 0 1)
  · refine (p.finite_setOf_isRoot hp).subset ?_
    rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    exact hx
  · have := injOn_circleMap_of_abs_sub_le (c := (0:ℂ)) (a := 0) (b := 2 * π) one_ne_zero
      (by simp [abs_of_nonneg two_pi_pos.le])
    rw [Set.uIoc_of_le two_pi_pos.le] at this
    exact this.mono Set.inter_subset_right

p2m_alias "P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.Polynomial.finite_setOf_eval_circleMap_eq_zero" "Polynomial.finite_setOf_eval_circleMap_eq_zero"
private theorem _root_.Polynomial.circleParamMeasure_setOf_eval_circleMap_eq_zero {p : Polynomial ℂ}
    (hp : p ≠ 0) : circleParamMeasure {x | p.eval (circleMap 0 1 x) = 0} = 0 := by
  rw [circleParamMeasure, Measure.restrict_apply' measurableSet_Ioc]
  exact (Polynomial.finite_setOf_eval_circleMap_eq_zero hp).measure_zero _

p2m_alias "P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.Polynomial.circleParamMeasure_setOf_eval_circleMap_eq_zero" "Polynomial.circleParamMeasure_setOf_eval_circleMap_eq_zero"
theorem measurableSet_setOf_eval_circleMap_eq_zero (P : MvPolynomial (Fin n) ℂ) :
    MeasurableSet {θ : Fin n → ℝ | eval (fun i ↦ circleMap 0 1 (θ i)) P = 0} :=
  (isClosed_singleton.preimage (continuous_eval_circleMap P)).measurableSet

theorem ae_eval_circleMap_ne_zero :
    ∀ {n : ℕ} {P : MvPolynomial (Fin n) ℂ}, P ≠ 0 →
      ∀ᵐ θ ∂(torusMeasure n), eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP
    obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨_, eq_C_of_isEmpty P⟩
    have hc : c ≠ 0 := by rintro rfl; simp at hP
    exact ae_of_all _ fun θ ↦ by simpa using hc
  | succ n ih =>
    intro P hP
    set S := {θ : Fin (n + 1) → ℝ | eval (fun i ↦ circleMap 0 1 (θ i)) P = 0} with hS_def
    have hS : MeasurableSet S := measurableSet_setOf_eval_circleMap_eq_zero P
    rw [ae_iff]
    simp only [ne_eq, not_not]
    change torusMeasure (n + 1) S = 0
    have hpre : MeasurableSet ((torusSplit n).symm ⁻¹' S) := hS.preimage (torusSplit n).symm.measurable
    rw [← (measurePreserving_torusSplit n).symm.measure_preimage hS.nullMeasurableSet,
      Measure.prod_apply_symm hpre, lintegral_eq_zero_iff' (measurable_measure_prodMk_right hpre).aemeasurable]
    set k := (finSuccEquiv ℂ n P).natDegree
    have hQ : (finSuccEquiv ℂ n P).coeff k ≠ 0 := by
      simpa [k] using Polynomial.leadingCoeff_ne_zero.mpr (finSuccEquiv_ne_zero hP)
    filter_upwards [ih hQ] with θ' hθ'
    have hfib : torusFiber P θ' ≠ 0 := fun h ↦ hθ' (by rw [← coeff_torusFiber, h, Polynomial.coeff_zero])
    have : (fun x : ℝ ↦ (x, θ')) ⁻¹' ((torusSplit n).symm ⁻¹' S) =
        {x | (torusFiber P θ').eval (circleMap 0 1 x) = 0} := by
      ext x
      simp [hS_def, torusSplit_symm_apply, eval_circleMap_cons, -MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp only [Pi.zero_apply, this]
    exact Polynomial.circleParamMeasure_setOf_eval_circleMap_eq_zero hfib

end MvPolynomial
p2m_reactivate "P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.MvPolynomial"

theorem solution {n : ℕ} {P : MvPolynomial (Fin n) ℂ} (hP : P ≠ 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (MvPolynomial.torusBox n)),
      MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by
  rw [MvPolynomial.volume_restrict_torusBox]
  exact MvPolynomial.ae_eval_circleMap_ne_zero hP

end S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero
end P2MW
export P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero (solution)
