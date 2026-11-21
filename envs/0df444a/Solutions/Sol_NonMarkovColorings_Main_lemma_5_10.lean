-- Prove2me | solution 1 for NonMarkovColorings.Main.lemma_5_10
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:02:14.191221+00:00
-- url     : https://prove2.me/submissions/c0206fa1-e87c-490b-9d98-b3c5d437fd50

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (μ : ℝ) (hμ : 0 < μ) (X : Ω → ℝ)
    (hX : Measurable X) (hlaw : P.map X = ProbabilityTheory.expMeasure (1 / μ))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω, A.indicator X ω ∂P ≤
      P.real A * (μ * Real.log (Real.exp 1 / P.real A) + 1) := by
  classical
  set p : ℝ := P.real A with hp
  set f : Ω → ℝ := A.indicator X with hf
  have hμpos : (0 : ℝ) < 1 / μ := by positivity
  haveI hprob : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 / μ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hμpos
  have hp0 : 0 ≤ p := by rw [hp]; exact measureReal_nonneg
  have hple : p ≤ 1 := by
    rw [hp]
    calc P.real A ≤ P.real Set.univ := measureReal_mono (Set.subset_univ A)
      _ = 1 := by simp
  -- `X` is nonnegative almost surely
  have hXnn : 0 ≤ᵐ[P] X := by
    show ∀ᵐ ω ∂P, 0 ≤ X ω
    rw [ae_iff]
    have hset : {ω : Ω | ¬ (0 ≤ X ω)} = X ⁻¹' Set.Iio 0 := by
      ext ω; simp
    rw [hset]
    have hmap : (P.map X) (Set.Iio 0) = P (X ⁻¹' Set.Iio 0) :=
      Measure.map_apply hX measurableSet_Iio
    rw [hlaw] at hmap
    rw [← hmap]
    have hzero : (ProbabilityTheory.expMeasure (1 / μ)) (Set.Iic 0) = 0 := by
      rw [← ProbabilityTheory.ofReal_cdf (ProbabilityTheory.expMeasure (1 / μ)) 0,
        ProbabilityTheory.cdf_expMeasure_eq hμpos 0]
      simp
    exact le_antisymm (hzero ▸ measure_mono Set.Iio_subset_Iic_self) (by simp)
  have hfnn : 0 ≤ᵐ[P] f := by
    filter_upwards [hXnn] with ω hω
    rw [hf]
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h]; exact hω
    · rw [Set.indicator_of_notMem h]
      exact le_refl 0
  have hfaesm : AEStronglyMeasurable f P := by
    rw [hf]
    exact hX.aestronglyMeasurable.indicator hA
  -- layer cake for `f`
  have hlayer : ∫ ω, f ω ∂P = (∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t < f ω}).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hfnn hfaesm,
      lintegral_eq_lintegral_meas_lt P hfnn hfaesm.aemeasurable]
  -- the survival function of the exponential law
  have hsurv : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} = ENNReal.ofReal (Real.exp (-(t / μ))) := by
    intro t ht
    have hset : {ω : Ω | t < X ω} = X ⁻¹' Set.Ioi t := by
      ext ω; simp
    have h1 : P (X ⁻¹' Set.Ioi t) = (ProbabilityTheory.expMeasure (1 / μ)) (Set.Ioi t) := by
      rw [← Measure.map_apply hX measurableSet_Ioi, hlaw]
    rw [hset, h1, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    have hcompl : Set.Ioi t = (Set.Iic t)ᶜ := by ext x; simp
    rw [hcompl]
    change (ProbabilityTheory.expMeasure (1 / μ)).real (Set.Iic t)ᶜ = Real.exp (-(t / μ))
    rw [measureReal_compl measurableSet_Iic]
    have hcdf : (ProbabilityTheory.expMeasure (1 / μ)).real (Set.Iic t) =
        1 - Real.exp (-((1 / μ) * t)) := by
      rw [← ProbabilityTheory.cdf_eq_real (ProbabilityTheory.expMeasure (1 / μ)) t,
        ProbabilityTheory.cdf_expMeasure_eq hμpos t, if_pos ht.le]
    rw [hcdf]
    have huniv : (ProbabilityTheory.expMeasure (1 / μ)).real Set.univ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [huniv]
    have hmul : (1 / μ) * t = t / μ := by ring
    rw [hmul]
    ring
  -- pointwise bound on the tail sets
  have hpt : ∀ t : ℝ, 0 < t →
      P {ω | t < f ω} ≤ ENNReal.ofReal (min p (Real.exp (-(t / μ)))) := by
    intro t ht
    have hset : {ω | t < f ω} = A ∩ {ω | t < X ω} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_inter_iff, hf]
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        exact ⟨fun h1 => ⟨h, h1⟩, fun h1 => h1.2⟩
      · rw [Set.indicator_of_notMem h]
        exact ⟨fun h1 => absurd h1 (not_lt.mpr ht.le), fun h1 => absurd h1.1 h⟩
    rw [hset, ENNReal.ofReal_min, le_min_iff]
    constructor
    · calc P (A ∩ {ω | t < X ω}) ≤ P A := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal p := by
            rw [hp]
            exact (ENNReal.ofReal_toReal (measure_ne_top P A)).symm
    · calc P (A ∩ {ω | t < X ω}) ≤ P {ω | t < X ω} := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal (Real.exp (-(t / μ))) := hsurv t ht
  have hmono : ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t < f ω} ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min p (Real.exp (-(t / μ)))) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht
  have hInt : IntegrableOn (fun t : ℝ => min p (Real.exp (-(t / μ)))) (Set.Ioi 0) := by
    have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-(1 / μ)) * t)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hμpos
    refine Integrable.mono hbase ?_ ?_
    · have hc : Continuous (fun t : ℝ => min p (Real.exp (-(t / μ)))) :=
        continuous_const.min (Real.continuous_exp.comp (continuous_id.div_const μ).neg)
      exact hc.aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_min hp0 (Real.exp_pos _).le), abs_of_pos (Real.exp_pos _)]
      have harg : -(t / μ) = (-(1 / μ)) * t := by field_simp
      rw [harg]
      exact min_le_right _ _
  have hlintegral_eq : ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (min p (Real.exp (-(t / μ))))
      = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ)))) :=
    (ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun t => le_min hp0 (Real.exp_pos _).le))).symm
  have hb_ne_top : (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (min p (Real.exp (-(t / μ))))) ≠ ⊤ := by
    rw [hlintegral_eq]
    exact ENNReal.ofReal_ne_top
  -- value of the model integral
  have hval : ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ))) ≤
      μ * p * (1 - Real.log p) := by
    rcases eq_or_lt_of_le hp0 with hpz | hppos
    · have hzero : (fun t : ℝ => min p (Real.exp (-(t / μ)))) = fun _ => 0 := by
        funext t
        rw [← hpz]
        exact min_eq_left (Real.exp_pos _).le
      rw [hzero, ← hpz]
      simp
    · have hlogp : Real.log p ≤ 0 := Real.log_nonpos hp0 hple
      set t0 : ℝ := -μ * Real.log p with ht0
      have ht0nn : 0 ≤ t0 := by rw [ht0]; nlinarith
      have hexp_t0 : Real.exp (-(t0 / μ)) = p := by
        have h1 : -(t0 / μ) = Real.log p := by
          rw [ht0]; field_simp
        rw [h1, Real.exp_log hppos]
      have hdisj : Disjoint (Set.Ioc 0 t0) (Set.Ioi t0) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx' (not_lt.mpr hx.2)
      have hunion : Set.Ioc 0 t0 ∪ Set.Ioi t0 = Set.Ioi (0 : ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (h | h)
          · exact h.1
          · linarith
        · intro h
          by_cases hx : x ≤ t0
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr (by linarith)
      have hI1 : IntegrableOn (fun t : ℝ => min p (Real.exp (-(t / μ)))) (Set.Ioc 0 t0) :=
        hInt.mono_set Set.Ioc_subset_Ioi_self
      have hI2 : IntegrableOn (fun t : ℝ => min p (Real.exp (-(t / μ)))) (Set.Ioi t0) :=
        hInt.mono_set (Set.Ioi_subset_Ioi ht0nn)
      have hμsplit : (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
          = (volume : Measure ℝ).restrict (Set.Ioc 0 t0)
            + (volume : Measure ℝ).restrict (Set.Ioi t0) := by
        rw [← hunion]
        exact Measure.restrict_union hdisj measurableSet_Ioi
      have hsplit : ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ)))
          = (∫ t in Set.Ioc 0 t0, min p (Real.exp (-(t / μ))))
            + (∫ t in Set.Ioi t0, min p (Real.exp (-(t / μ)))) := by
        rw [hμsplit]
        exact integral_add_measure hI1 hI2
      have h1 : ∫ t in Set.Ioc 0 t0, min p (Real.exp (-(t / μ))) = p * t0 := by
        have hcongr : ∫ t in Set.Ioc 0 t0, min p (Real.exp (-(t / μ)))
            = ∫ t in Set.Ioc 0 t0, p := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          refine min_eq_left ?_
          have h2 : t / μ ≤ t0 / μ := by
            gcongr
            exact ht.2
          have h3 : t0 / μ = -Real.log p := by rw [ht0]; field_simp
          calc p = Real.exp (Real.log p) := (Real.exp_log hppos).symm
            _ ≤ Real.exp (-(t / μ)) := by
                apply Real.exp_le_exp.mpr
                linarith
        rw [hcongr, ← intervalIntegral.integral_of_le ht0nn, intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        ring
      have h2 : ∫ t in Set.Ioi t0, min p (Real.exp (-(t / μ))) = p * μ := by
        have hcongr : ∫ t in Set.Ioi t0, min p (Real.exp (-(t / μ)))
            = ∫ t in Set.Ioi t0, Real.exp (-(t / μ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          refine min_eq_right ?_
          have h2 : t0 / μ < t / μ := by
            gcongr
            exact ht
          have h3 : t0 / μ = -Real.log p := by rw [ht0]; field_simp
          calc Real.exp (-(t / μ)) ≤ Real.exp (Real.log p) := by
                apply Real.exp_le_exp.mpr
                linarith
            _ = p := Real.exp_log hppos
        rw [hcongr]
        have hexpint : ∫ t in Set.Ioi t0, Real.exp (-(t / μ)) = Real.exp (-(t0 / μ)) * μ := by
          have hbase : ∫ t in Set.Ioi t0, Real.exp ((-(1 / μ)) * t)
              = -Real.exp ((-(1 / μ)) * t0) / (-(1 / μ)) :=
            integral_exp_mul_Ioi (neg_neg_of_pos hμpos) t0
          have hcongr2 : ∫ t in Set.Ioi t0, Real.exp (-(t / μ))
              = ∫ t in Set.Ioi t0, Real.exp ((-(1 / μ)) * t) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _
            congr 1
            field_simp
          rw [hcongr2, hbase]
          have harg : (-(1 / μ)) * t0 = -(t0 / μ) := by field_simp
          rw [harg]
          field_simp
        rw [hexpint, hexp_t0]
      have hEq : ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ)))
          = μ * p * (1 - Real.log p) := by
        calc ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ)))
            = (∫ t in Set.Ioc 0 t0, min p (Real.exp (-(t / μ))))
              + (∫ t in Set.Ioi t0, min p (Real.exp (-(t / μ)))) := hsplit
          _ = p * t0 + p * μ := by linarith [h1, h2]
          _ = μ * p * (1 - Real.log p) := by rw [ht0]; field_simp; ring
      rw [hEq]
  -- comparison with the right hand side
  have hRHS : μ * p * (1 - Real.log p) ≤ p * (μ * Real.log (Real.exp 1 / p) + 1) := by
    rcases eq_or_lt_of_le hp0 with hpz | hppos
    · have hp0' : p = 0 := hpz.symm
      rw [hp0']
      simp
    · have hlog : Real.log (Real.exp 1 / p) = 1 - Real.log p := by
        rw [Real.log_div (Real.exp_ne_zero 1) hppos.ne', Real.log_exp]
      rw [hlog]
      nlinarith [hp0]
  calc ∫ ω, f ω ∂P
      = (∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t < f ω}).toReal := hlayer
    _ ≤ (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (min p (Real.exp (-(t / μ))))).toReal :=
        ENNReal.toReal_mono hb_ne_top hmono
    _ = (ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ))))).toReal := by
        rw [hlintegral_eq]
    _ = ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ))) := by
        have hnn : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), min p (Real.exp (-(t / μ))) :=
          integral_nonneg (f := fun t : ℝ => min p (Real.exp (-(t / μ))))
            (fun t => le_min hp0 (Real.exp_pos _).le)
        rw [ENNReal.toReal_ofReal hnn]
    _ ≤ μ * p * (1 - Real.log p) := hval
    _ ≤ p * (μ * Real.log (Real.exp 1 / p) + 1) := hRHS
