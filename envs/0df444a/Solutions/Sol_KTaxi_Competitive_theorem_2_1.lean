-- Prove2me | solution 1 for KTaxi.Competitive.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:07:14.936775+00:00
-- url     : https://prove2.me/submissions/4931eea6-5687-4f9f-8087-182e5d7c3912

import Mathlib

open MeasureTheory ProbabilityTheory Set

lemma exp_tail (r : ℝ) (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    expMeasure r (Ici x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have hsing : expMeasure r {x} = 0 := by
    have hac : expMeasure r ≪ volume := by
      rw [expMeasure, gammaMeasure]; exact withDensity_absolutelyContinuous _ _
    exact hac (Real.volume_singleton)
  have hIio : (expMeasure r).real (Iio x) = (expMeasure r).real (Iic x) := by
    rw [← Iio_union_right, measureReal_union (by simp) (measurableSet_singleton x)]
    rw [measureReal_def (s := {x}), hsing]; simp
  have hcdf : (expMeasure r).real (Iic x) = 1 - Real.exp (-(r * x)) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hx]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (expMeasure r) (Ici x))]
  congr 1
  have hc : Ici x = (Iio x)ᶜ := by ext; simp
  rw [← measureReal_def, hc, probReal_compl_eq_one_sub measurableSet_Iio, hIio, hcdf]; ring

lemma race_integral (r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    ∫⁻ x in Ici (0:ℝ), ENNReal.ofReal (r * Real.exp (-(R * x))) = ENNReal.ofReal (r / R) := by
  have hI : ∫ x in Ioi (0:ℝ), r * Real.exp (-(R * x)) = r / R := by
    rw [integral_const_mul]
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := R) one_pos hR
    simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at this
    rw [this]; ring
  have hint : IntegrableOn (fun x => r * Real.exp (-(R * x))) (Ioi (0:ℝ)) := by
    apply Integrable.of_integral_ne_zero; rw [hI]; positivity
  rw [← setLIntegral_congr Ioi_ae_eq_Ici, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => by positivity)), hI]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (ζ : Fin m → Ω → ℝ) (rate : Fin m → ℝ) (hrate : ∀ i, 0 < rate i)
    (hmeas : ∀ i, Measurable (ζ i)) (hind : iIndepFun ζ P)
    (hlaw : ∀ i, P.map (ζ i) = expMeasure (rate i)) (i : Fin m) :
    P {ω | ∀ j, ζ i ω ≤ ζ j ω} = ENNReal.ofReal (rate i / ∑ j, rate j) := by
  cases m with
  | zero => exact i.elim0
  | succ n =>
  set μ : Fin (n + 1) → Measure ℝ := fun j => expMeasure (rate j) with hμ
  haveI : ∀ j, IsProbabilityMeasure (μ j) := fun j => isProbabilityMeasure_expMeasure (hrate j)
  have hlawvec : P.map (fun ω j => ζ j ω) = Measure.pi μ := by
    rw [hind.map_fun_eq_pi_map (fun j => (hmeas j).aemeasurable)]
    congr 1; funext j; exact hlaw j
  set S : Set (Fin (n + 1) → ℝ) := {y | ∀ j, y i ≤ y j} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋂ j, {y : Fin (n + 1) → ℝ | y i ≤ y j} := by ext; simp [hS]
    rw [this]
    exact MeasurableSet.iInter (fun j => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
  have h1 : P {ω | ∀ j, ζ i ω ≤ ζ j ω} = Measure.pi μ S := by
    rw [← hlawvec, Measure.map_apply (measurable_pi_lambda _ hmeas) hSm]; rfl
  rw [h1]
  have hmp := measurePreserving_piFinSuccAbove μ i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  set T : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j', p.1 ≤ p.2 j'} with hT
  have hpre : e.symm ⁻¹' S = T := by
    ext ⟨x, z⟩
    simp only [Set.mem_preimage, hS, hT, Set.mem_ofPred_eq, he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [Fin.forall_iff_succAbove i]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hTm : MeasurableSet T := by
    have : T = ⋂ j', {p : ℝ × (Fin n → ℝ) | p.1 ≤ p.2 j'} := by ext; simp [hT]
    rw [this]
    exact MeasurableSet.iInter (fun j' => measurableSet_le measurable_fst
      ((measurable_pi_apply j').comp measurable_snd))
  rw [← hmp.symm.measure_preimage hSm.nullMeasurableSet, hpre, Measure.prod_apply hTm]
  have hsec : ∀ x : ℝ, (Prod.mk x ⁻¹' T) = Set.pi univ (fun _ : Fin n => Ici x) := by
    intro x; ext z
    simp only [Set.mem_preimage, hT, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ici]
  simp_rw [hsec, Measure.pi_pi]
  -- outer integral against exp density
  rw [show μ i = expMeasure (rate i) from rfl, expMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (f := gammaPDF 1 (rate i))
      (measurable_gammaPDFReal 1 (rate i)).ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  set R := ∑ j, rate j with hR
  have hRsplit : R = rate i + ∑ j' : Fin n, rate (i.succAbove j') := by
    rw [hR, Fin.sum_univ_succAbove _ i]
  have hRpos : 0 < R := Finset.sum_pos (fun j _ => hrate j) Finset.univ_nonempty
  have hpt : ∀ x : ℝ, (gammaPDF 1 (rate i) * fun x => ∏ j' : Fin n, μ (i.succAbove j') (Ici x)) x =
      (Ici (0:ℝ)).indicator (fun x => ENNReal.ofReal (rate i * Real.exp (-(R * x)))) x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · simp [gammaPDF_of_neg hx, Set.indicator_of_notMem (show x ∉ Ici 0 from fun h => absurd h (by simpa using hx))]
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx), Pi.mul_apply, gammaPDF_of_nonneg hx,
        Real.Gamma_one, Real.rpow_one, sub_self, Real.rpow_zero, div_one, mul_one]
      simp only [hμ]
      rw [Finset.prod_congr rfl (fun j' _ => exp_tail (rate (i.succAbove j')) (hrate _) x hx),
        ← ENNReal.ofReal_prod_of_nonneg (fun j' _ => (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (mul_nonneg (hrate i).le (Real.exp_pos _).le)]
      congr 1
      rw [← Real.exp_sum, hRsplit, mul_assoc, ← Real.exp_add]
      congr 2
      simp only [neg_mul, Finset.sum_neg_distrib]
      rw [← Finset.sum_mul]; ring
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ici, race_integral (rate i) R (hrate i) hRpos]
