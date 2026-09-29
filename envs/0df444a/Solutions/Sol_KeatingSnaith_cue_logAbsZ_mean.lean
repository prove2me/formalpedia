-- Prove2me | solution 1 for KeatingSnaith.cue_logAbsZ_mean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T21:16:24.646402+00:00
-- url     : https://prove2.me/submissions/14e8556c-3939-46af-9e2b-b0c716baa149

import Mathlib
import Definitions.Def_keating_snaith_cue

set_option autoImplicit false

namespace KS951

open MeasureTheory Finset KeatingSnaith
open scoped Real

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def ptC (x : AddCircle (2 * Real.pi)) : ℂ := (AddCircle.toCircle x : ℂ)

lemma ptC_mk (t : ℝ) : ptC (t : AddCircle (2 * Real.pi)) = Complex.exp (t * Complex.I) := by
  have h : 2 * Real.pi / (2 * Real.pi) * t = t := by
    rw [div_self (by positivity), one_mul]
  simp only [ptC, AddCircle.toCircle_apply_mk, h, Circle.coe_exp]

lemma ptC_add (x y : AddCircle (2 * Real.pi)) : ptC (x + y) = ptC x * ptC y := by
  simp only [ptC, AddCircle.toCircle_add, Circle.coe_mul]

lemma norm_ptC (x : AddCircle (2 * Real.pi)) : ‖ptC x‖ = 1 := Circle.norm_coe _

lemma continuous_ptC : Continuous ptC :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

lemma ptC_eq_one_iff (x : AddCircle (2 * Real.pi)) : ptC x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : AddCircle.toCircle x = AddCircle.toCircle (0 : AddCircle (2 * Real.pi)) := by
      apply Subtype.ext
      rw [AddCircle.toCircle_zero]
      exact h
    exact AddCircle.injective_toCircle (by positivity) h1
  · rintro rfl
    simp [ptC, AddCircle.toCircle_zero]

noncomputable def dens (N : ℕ) (z : Fin N → AddCircle (2 * Real.pi)) : ℝ :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
    ‖ptC (z p.1) - ptC (z p.2)‖ ^ 2

noncomputable def lg (x : AddCircle (2 * Real.pi)) : ℝ := Real.log ‖1 - ptC x‖

noncomputable def Ft (N : ℕ) (z : Fin N → AddCircle (2 * Real.pi)) : ℝ :=
  dens N z * Real.log ‖∏ n, (1 - ptC (z n))‖

lemma continuous_dens (N : ℕ) : Continuous (dens N) := by
  unfold dens
  exact continuous_finsetProd _ (fun p _ =>
    ((continuous_ptC.comp (continuous_apply p.1)).sub
      (continuous_ptC.comp (continuous_apply p.2))).norm.pow 2)

lemma measurable_Ft (N : ℕ) : Measurable (Ft N) := by
  unfold Ft
  exact (continuous_dens N).measurable.mul (Real.measurable_log.comp
    (continuous_finsetProd _ (fun n _ =>
      continuous_const.sub (continuous_ptC.comp (continuous_apply n)))).norm.measurable)

lemma measurable_lg : Measurable lg := by
  unfold lg
  exact Real.measurable_log.comp (continuous_const.sub continuous_ptC).norm.measurable

lemma box_eq (N : ℕ) :
    ∫ θ in phaseBox N, cueDensity N θ • logAbsZ N θ = ∫ z, Ft N z := by
  have hmp : MeasurePreserving (fun (θ : Fin N → ℝ) i => ((θ i : ℝ) : AddCircle (2 * Real.pi)))
      (volume.restrict (phaseBox N)) volume := by
    have h1 : volume.restrict (phaseBox N) =
        Measure.pi (fun _ : Fin N => volume.restrict (Set.Ioc (0:ℝ) (0 + 2 * Real.pi))) := by
      rw [phaseBox, zero_add, volume_pi, Measure.restrict_pi_pi]
    rw [h1, volume_pi]
    exact measurePreserving_pi _ _ (fun _ => AddCircle.measurePreserving_mk (2 * Real.pi) 0)
  have := integral_map hmp.aemeasurable (measurable_Ft N).aestronglyMeasurable
  rw [hmp.map_eq] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [Ft, dens, ptC_mk, cueDensity, logAbsZ, charPoly, smul_eq_mul]

lemma dens_shift (N : ℕ) (z : Fin N → AddCircle (2 * Real.pi)) (c : AddCircle (2 * Real.pi)) :
    dens N (z + fun _ => c) = dens N z := by
  unfold dens
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp only [Pi.add_apply, ptC_add]
  rw [← sub_mul, norm_mul, norm_ptC, mul_one]

lemma Ft_shift (N : ℕ) (z : Fin N → AddCircle (2 * Real.pi)) (c : AddCircle (2 * Real.pi))
    (h : ∀ n, z n + c ≠ 0) :
    Ft N (z + fun _ => c) = dens N z * ∑ n, lg (z n + c) := by
  unfold Ft
  rw [dens_shift, norm_prod, Real.log_prod]
  · rfl
  · intro n _
    simp only [Pi.add_apply]
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro h1
    exact h n ((ptC_eq_one_iff _).mp h1.symm)

lemma lg_mk (t : ℝ) : lg (t : AddCircle (2 * Real.pi)) = Real.log ‖circleMap 0 1 t - 1‖ := by
  simp only [lg, ptC_mk, circleMap, zero_add, Complex.ofReal_one, one_mul]
  rw [← norm_neg, neg_sub]

lemma lg_integrable_and_zero : Integrable lg ∧ ∫ c, lg c = 0 := by
  have hmp := AddCircle.measurePreserving_mk (2 * Real.pi) 0
  rw [zero_add] at hmp
  have hci : CircleIntegrable (fun x => Real.log ‖x - 1‖) 0 1 := circleIntegrable_log_norm_sub_const 1
  rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at hci
  constructor
  · rw [← hmp.integrable_comp measurable_lg.aestronglyMeasurable]
    have : (lg ∘ ((↑) : ℝ → AddCircle (2 * Real.pi))) = fun t => Real.log ‖circleMap 0 1 t - 1‖ := by
      funext t; exact lg_mk t
    rw [this]
    exact hci
  · have h2 := integral_map hmp.aemeasurable measurable_lg.aestronglyMeasurable
    rw [hmp.map_eq] at h2
    rw [h2]
    have h3 : Real.circleAverage (fun x => Real.log ‖x - 1‖) 0 1 = 0 :=
      circleAverage_log_norm_sub_const₁ (by simp)
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)] at h3
    rw [smul_eq_mul] at h3
    have h4 := (mul_eq_zero.mp h3).resolve_left (by positivity)
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun t => lg_mk t))).trans h4

lemma inner_zero (N : ℕ) (z : Fin N → AddCircle (2 * Real.pi)) :
    ∫ c, Ft N (z + fun _ => c) = 0 := by
  have hae : ∀ᵐ c : AddCircle (2 * Real.pi), ∀ n, z n + c ≠ 0 := by
    rw [ae_all_iff]
    intro n
    have hs : volume ({-z n} : Set (AddCircle (2 * Real.pi))) = 0 := by
      rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
      simp
    have : {c : AddCircle (2 * Real.pi) | ¬ (z n + c ≠ 0)} ⊆ {-z n} := by
      intro c hc
      simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hc
      simp only [Set.mem_singleton_iff]
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
    exact measure_mono_null this hs
  rw [integral_congr_ae (hae.mono (fun c hc => Ft_shift N z c hc))]
  rw [integral_const_mul, integral_finsetSum]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro n _
    rw [integral_add_left_eq_self (fun c => lg c) (z n)]
    exact lg_integrable_and_zero.2
  · intro n _
    exact lg_integrable_and_zero.1.comp_add_left (z n)

lemma torus_zero (N : ℕ) : ∫ z, Ft N z = 0 := by
  by_cases hI : Integrable (Ft N)
  swap
  · exact integral_undef hI
  have hmp : MeasurePreserving
      (fun p : AddCircle (2 * Real.pi) × (Fin N → AddCircle (2 * Real.pi)) =>
        (id p.1, (fun c z => z + fun _ => c) p.1 p.2))
      ((volume : Measure (AddCircle (2 * Real.pi))).prod (volume : Measure (Fin N → AddCircle (2 * Real.pi))))
      ((volume : Measure (AddCircle (2 * Real.pi))).prod (volume : Measure (Fin N → AddCircle (2 * Real.pi)))) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure (AddCircle (2 * Real.pi))))
      (μc := (volume : Measure (Fin N → AddCircle (2 * Real.pi))))
      (μd := (volume : Measure (Fin N → AddCircle (2 * Real.pi))))
      (g := fun c z => z + fun _ => c) ?_ ?_
    · exact (continuous_snd.add (continuous_pi fun _ => continuous_fst)).measurable
    · exact Filter.Eventually.of_forall (fun c => (measurePreserving_add_right volume (fun _ => c)).map_eq)
  have h2 : Integrable (fun p : AddCircle (2 * Real.pi) × (Fin N → AddCircle (2 * Real.pi)) => Ft N p.2)
      ((volume : Measure (AddCircle (2 * Real.pi))).prod volume) := hI.comp_snd volume
  have hprod : Integrable (Function.uncurry fun (c : AddCircle (2 * Real.pi))
      (z : Fin N → AddCircle (2 * Real.pi)) => Ft N (z + fun _ => c))
      ((volume : Measure (AddCircle (2 * Real.pi))).prod volume) := by
    have := (hmp.integrable_comp h2.aestronglyMeasurable).mpr h2
    exact this
  have hswap := integral_integral_swap hprod
  have hL : ∫ c : AddCircle (2 * Real.pi), ∫ z, Ft N (z + fun _ => c) = (2 * Real.pi) * ∫ z, Ft N z := by
    simp_rw [integral_add_right_eq_self (fun z => Ft N z)]
    rw [integral_const, smul_eq_mul, Measure.real, AddCircle.measure_univ,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hL] at hswap
  simp_rw [inner_zero] at hswap
  rw [integral_zero] at hswap
  rcases mul_eq_zero.mp hswap with h | h
  · exfalso; exact (by positivity : (2 * Real.pi) ≠ 0) h
  · exact h

end KS951

open KeatingSnaith in
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    KeatingSnaith.cueAverage N (fun θ => KeatingSnaith.logAbsZ N θ) = 0 := by
  unfold KeatingSnaith.cueAverage
  rw [KS951.box_eq, KS951.torus_zero, smul_zero]
