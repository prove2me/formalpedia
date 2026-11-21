-- Prove2me | solution 1 for MasulloRepair.compact_window_measure_and_norm_identification
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T02:12:58.957779+00:00
-- url     : https://prove2.me/submissions/d54af31f-213e-41fe-b96d-e72a05c10872

import Definitions.Def_MasulloRepair_WindowL2

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

private lemma source_window_measure (a s : ℝ) (n : ℕ) :
    windowMeasure (halflineBaseMeasure a s) n =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal
          (max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t)) := by
  dsimp [windowMeasure, halflineBaseMeasure]
  have hweight : Measurable (windowWeight n) := by
    change Measurable (fun t : ℝ => ENNReal.ofReal (max 1 (t^(2*n))))
    fun_prop
  rw [← withDensity_mul _ (by fun_prop) hweight]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hp : t^(2*(a+(n : ℝ))) = t^(2*a) * t^(2*n) := by
    rw [mul_add, Real.rpow_add ht,
      show (2 : ℝ)*(n : ℝ) = ((2*n : ℕ) : ℝ) by simp, Real.rpow_natCast]
  have hw : max (t^(2*a)) (t^(2*(a+(n : ℝ)))) = t^(2*a) * max 1 (t^(2*n)) := by
    rw [hp, mul_max_of_nonneg _ _ (Real.rpow_nonneg ht.le _), mul_one]
  change ENNReal.ofReal (t^(2*a) * (1+(Real.log t)^2)^(s/2) / t) *
      ENNReal.ofReal (max 1 (t^(2*n))) = _
  rw [← ENNReal.ofReal_mul (by positivity), hw]
  congr 1
  ring

theorem solution (a s : ℝ) (n : ℕ) :
    windowMeasure (halflineBaseMeasure a s) n =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal
          (max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t)) ∧
    ∀ f : Lp ℂ 2 (windowMeasure (halflineBaseMeasure a s) n),
      IntegrableOn (fun t : ℝ => ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) *
        (1+(Real.log t)^2)^(s/2) / t) (Ioi 0) ∧
      ‖f‖ = Real.sqrt (∫ t in Ioi (0 : ℝ),
        ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t) := by
  refine ⟨source_window_measure a s n, ?_⟩
  intro f
  let d : ℝ → ℝ := fun t =>
    max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t
  have hd : Measurable (fun t => ENNReal.ofReal (d t)) := by dsimp [d]; fun_prop
  have hdtop : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ENNReal.ofReal (d t) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hdn (t : ℝ) (ht : 0 < t) : 0 ≤ d t := by
    dsimp [d]
    positivity
  have hint : Integrable (fun t : ℝ => ‖f t‖^2) (windowMeasure (halflineBaseMeasure a s) n) := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.integrable_inner (𝕜 := ℝ) f f)
  have hnorm : ‖f‖^2 = ∫ t, ‖f t‖^2 ∂windowMeasure (halflineBaseMeasure a s) n := by
    calc
      ‖f‖^2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
      _ = ∫ t, inner ℝ (f t) (f t) ∂windowMeasure (halflineBaseMeasure a s) n := L2.inner_def f f
      _ = ∫ t, ‖f t‖^2 ∂windowMeasure (halflineBaseMeasure a s) n := by
        simp only [real_inner_self_eq_norm_sq]
  have hint' : Integrable (fun t : ℝ => ‖f t‖^2)
      ((volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (d t))) := by
    simpa only [source_window_measure a s n] using hint
  have heq : (fun t : ℝ => (ENNReal.ofReal (d t)).toReal • ‖f t‖^2)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun t : ℝ => ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) *
          (1+(Real.log t)^2)^(s/2) / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.toReal_ofReal (hdn t ht), smul_eq_mul]
    dsimp [d]
    ring
  have hactual : IntegrableOn (fun t : ℝ => ‖f t‖^2 *
      max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t) (Ioi 0) :=
    ((integrable_withDensity_iff_integrable_smul' hd hdtop).mp hint').congr heq
  refine ⟨hactual, ?_⟩
  have hi : (∫ t, ‖f t‖^2 ∂windowMeasure (halflineBaseMeasure a s) n) =
      ∫ t in Ioi (0 : ℝ), ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) *
        (1+(Real.log t)^2)^(s/2) / t := by
    calc
      _ = ∫ t, ‖f t‖^2 ∂(volume.restrict (Ioi (0 : ℝ))).withDensity
          (fun t => ENNReal.ofReal (d t)) :=
        congrArg (fun ν : Measure ℝ => ∫ t, ‖f t‖^2 ∂ν) (source_window_measure a s n)
      _ = ∫ t in Ioi (0 : ℝ), (ENNReal.ofReal (d t)).toReal • ‖f t‖^2 :=
        integral_withDensity_eq_integral_toReal_smul hd hdtop _
      _ = _ := integral_congr_ae heq
  rw [← hi, ← hnorm, Real.sqrt_sq (norm_nonneg f)]

#print axioms solution
