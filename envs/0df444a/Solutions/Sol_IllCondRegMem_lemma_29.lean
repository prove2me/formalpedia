-- Prove2me | solution 1 for IllCondRegMem.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T03:17:18.315809+00:00
-- url     : https://prove2.me/submissions/2e9e7c68-0b0b-4ee7-be39-629a26f225be

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set ENNReal

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    betaMeasure a b (Set.Iic t) ≤ ENNReal.ofReal ((Real.exp 1 * (a + b) * t / a) ^ a) := by
  rcases eq_or_lt_of_le ht0 with ht_eq | htpos
  · -- t = 0
    subst ht_eq
    have hzero : betaMeasure a b (Set.Iic 0) = 0 := by
      rw [betaMeasure, withDensity_apply _ measurableSet_Iic]
      rw [setLIntegral_eq_zero measurableSet_Iic]
      intro x hx
      exact betaPDF_eq_zero_of_nonpos hx
    have hrhs : (Real.exp 1 * (a + b) * 0 / a) ^ a = 0 := by
      rw [mul_zero, zero_div, Real.zero_rpow ha.ne']
    rw [hzero, hrhs, ENNReal.ofReal_zero]
  -- from now on t > 0
  set C : ℝ := 1 / beta a b with hC
  have hBpos : 0 < beta a b := beta_pos ha hb
  have hCpos : 0 < C := by rw [hC]; exact one_div_pos.mpr hBpos
  have hCnonneg : 0 ≤ C := hCpos.le
  -- value of the density on (0,1)
  have hPDFval : ∀ x : ℝ, 0 < x → x < 1 →
      betaPDF a b x = ENNReal.ofReal (C * x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    intro x hx0 hx1
    rw [betaPDF_of_pos_lt_one hx0 hx1, hC]
  -- normalization of the density on (0,1)
  have hnorm : ∫⁻ u in Set.Ioo 0 1, betaPDF a b u = 1 := by
    calc ∫⁻ u in Set.Ioo 0 1, betaPDF a b u
        = ∫⁻ u in Set.Ioo 0 1,
            ENNReal.ofReal (1 / beta a b * u ^ (a - 1) * (1 - u) ^ (b - 1)) := by
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro u hu
            exact betaPDF_of_pos_lt_one hu.1 hu.2
      _ = ∫⁻ u, betaPDF a b u := (lintegral_betaPDF).symm
      _ = 1 := lintegral_betaPDF_eq_one ha hb
  -- the density vanishes on Iic 0
  have hsupp : ∫⁻ x in Set.Iic t, betaPDF a b x = ∫⁻ x in Set.Ioc 0 t, betaPDF a b x := by
    have hI : Set.Iic t = Set.Iic 0 ∪ Set.Ioc 0 t := by
      ext x
      constructor
      · intro hx
        rcases lt_or_ge x 0 with h | h
        · exact Or.inl h.le
        · rcases eq_or_lt_of_le h with h0 | h0
          · exact Or.inl (le_of_eq h0.symm)
          · exact Or.inr ⟨h0, hx⟩
      · rintro (h | h)
        · exact h.trans ht0
        · exact h.2
    rw [hI, lintegral_union measurableSet_Ioc (by
      rw [disjoint_left]
      intro x hx1 hx2
      exact absurd hx1 (not_le_of_gt hx2.1)),
      setLIntegral_eq_zero measurableSet_Iic (fun x hx => betaPDF_eq_zero_of_nonpos hx),
      zero_add]
  have hstep : betaMeasure a b (Set.Iic t) = ∫⁻ x in Set.Iic t, betaPDF a b x := by
    rw [betaMeasure, withDensity_apply _ measurableSet_Iic]
  -- the point t is null
  have hae_ne : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ t := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬ x ≠ t} = {t} := by
      ext x
      constructor
      · intro h
        exact not_not.mp h
      · intro h
        have hx : x = t := Set.mem_singleton_iff.mp h
        rw [hx]
        exact not_not.mpr rfl
    rw [hset]
    exact measure_singleton t
  by_cases hb1 : 1 ≤ b
  · -- Case b ≥ 1
    have hle1 : ∫⁻ x in Set.Ioc 0 t, betaPDF a b x ≤
        ∫⁻ x in Set.Ioo 0 t, ENNReal.ofReal (C * x ^ (a - 1)) := by
      rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_mono_ae
      filter_upwards [hae_ne] with x hxt
      by_cases hx : x ∈ Set.Ioc 0 t
      · rw [Set.indicator_of_mem hx]
        by_cases hx' : x ∈ Set.Ioo 0 t
        · rw [Set.indicator_of_mem hx']
          rw [hPDFval x hx'.1 (hx'.2.trans_le ht1)]
          apply ENNReal.ofReal_le_ofReal
          have h1x : 0 ≤ 1 - x := by linarith [hx'.2.trans_le ht1]
          have h1x' : 1 - x ≤ 1 := by linarith [hx'.1]
          have hpow : (1 - x) ^ (b - 1) ≤ 1 :=
            Real.rpow_le_one h1x h1x' (by linarith : 0 ≤ b - 1)
          calc C * x ^ (a - 1) * (1 - x) ^ (b - 1)
              = (C * x ^ (a - 1)) * (1 - x) ^ (b - 1) := by ring
            _ ≤ (C * x ^ (a - 1)) * 1 :=
                mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnonneg (Real.rpow_nonneg hx'.1.le _))
            _ = C * x ^ (a - 1) := by ring
        · exfalso
          have hxt' : x = t := by
            rcases hx with ⟨hx0, hxtle⟩
            exact le_antisymm hxtle (le_of_not_gt fun h => hx' ⟨hx0, h⟩)
          exact hxt hxt'
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hInt : ∫⁻ x in Set.Ioo 0 t, ENNReal.ofReal (C * x ^ (a - 1)) =
        ENNReal.ofReal (C * t ^ a / a) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0]
        rw [intervalIntegral.integral_const_mul]
        rw [integral_rpow (Or.inl (by linarith : -1 < a - 1)), show a - 1 + 1 = a by ring]
        rw [show (0 : ℝ) ^ a = 0 from Real.zero_rpow ha.ne', sub_zero]
        ring
      · show IntegrableOn (fun x : ℝ => C * x ^ (a - 1)) (Set.Ioo 0 t) volume
        rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht0]
        exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := a - 1)
          (by linarith)).const_mul C
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact mul_nonneg hCnonneg (Real.rpow_nonneg hx.1.le _)
    -- lower bound on C/a through the normalization
    set x0 : ℝ := a / (a + b) with hx0def
    have habpos : 0 < a + b := by linarith
    have hx0pos : 0 < x0 := by rw [hx0def]; positivity
    have hx0lt1 : x0 < 1 := by
      rw [hx0def, div_lt_one habpos]
      linarith
    set K : ℝ := (b / (a + b)) ^ (b - 1) with hKdef
    have hKpos : 0 < K := by
      rw [hKdef]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hsum : a / (a + b) + b / (a + b) = 1 := by
      field_simp
    have hlow : ∫⁻ u in Set.Ioo 0 x0, ENNReal.ofReal (C * K * u ^ (a - 1)) ≤
        ∫⁻ u in Set.Ioo 0 x0, betaPDF a b u := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro u hu
      rw [hPDFval u hu.1 (hu.2.trans hx0lt1)]
      apply ENNReal.ofReal_le_ofReal
      have hbK : b / (a + b) ≤ 1 - u := by
        have hlt : u < a / (a + b) := by
          have h := hu.2
          rwa [hx0def] at h
        linarith
      have hpow : K ≤ (1 - u) ^ (b - 1) := by
        rw [hKdef]
        exact Real.rpow_le_rpow (by positivity) hbK (by linarith : 0 ≤ b - 1)
      calc C * K * u ^ (a - 1)
          = (C * u ^ (a - 1)) * K := by ring
        _ ≤ (C * u ^ (a - 1)) * (1 - u) ^ (b - 1) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnonneg (Real.rpow_nonneg hu.1.le _))
        _ = C * u ^ (a - 1) * (1 - u) ^ (b - 1) := by ring
    have hlowint : ∫⁻ u in Set.Ioo 0 x0, ENNReal.ofReal (C * K * u ^ (a - 1)) =
        ENNReal.ofReal (C * K * x0 ^ a / a) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx0pos.le]
        rw [intervalIntegral.integral_const_mul]
        rw [integral_rpow (Or.inl (by linarith : -1 < a - 1)), show a - 1 + 1 = a by ring]
        rw [show (0 : ℝ) ^ a = 0 from Real.zero_rpow ha.ne', sub_zero]
        ring
      · show IntegrableOn (fun u : ℝ => C * K * u ^ (a - 1)) (Set.Ioo 0 x0) volume
        rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hx0pos.le]
        exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x0) (r := a - 1)
          (by linarith)).const_mul (C * K)
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact mul_nonneg (mul_nonneg hCnonneg hKpos.le) (Real.rpow_nonneg hu.1.le _)
    have hnorm_lower : ∫⁻ u in Set.Ioo 0 x0, betaPDF a b u ≤ 1 := by
      calc ∫⁻ u in Set.Ioo 0 x0, betaPDF a b u
          ≤ ∫⁻ u in Set.Ioo 0 1, betaPDF a b u :=
              lintegral_mono_set (Set.Ioo_subset_Ioo le_rfl hx0lt1.le)
        _ = 1 := hnorm
    have hle_real : C * K * x0 ^ a / a ≤ 1 := by
      have h1 : ENNReal.ofReal (C * K * x0 ^ a / a) ≤ ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_one]
        calc ENNReal.ofReal (C * K * x0 ^ a / a)
            = ∫⁻ u in Set.Ioo 0 x0, ENNReal.ofReal (C * K * u ^ (a - 1)) := hlowint.symm
          _ ≤ ∫⁻ u in Set.Ioo 0 x0, betaPDF a b u := hlow
          _ ≤ 1 := hnorm_lower
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp h1
    -- the e factor
    have hKexp : Real.exp (-a) ≤ K := by
      have hypos : 0 < 1 + a / b := by positivity
      have hlog : Real.log (1 + a / b) ≤ a / b := by
        have h := Real.log_le_sub_one_of_pos hypos
        rwa [add_sub_cancel_left] at h
      have hb_log : b * Real.log (1 + a / b) ≤ a := by
        calc b * Real.log (1 + a / b) ≤ b * (a / b) :=
              mul_le_mul_of_nonneg_left hlog hb.le
          _ = a := by field_simp
      have hpow_b : (1 + a / b) ^ b ≤ Real.exp a := by
        rw [Real.rpow_def_of_pos hypos, mul_comm]
        exact Real.exp_le_exp.mpr hb_log
      have hone : 1 ≤ 1 + a / b := by
        have h : 0 < a / b := by positivity
        linarith
      have hpow_le : (1 + a / b) ^ (b - 1) ≤ (1 + a / b) ^ b :=
        Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      have hpow_final : (1 + a / b) ^ (b - 1) ≤ Real.exp a := hpow_le.trans hpow_b
      have hpos_pow : 0 < (1 + a / b) ^ (b - 1) := Real.rpow_pos_of_pos hypos _
      have hbase : b / (a + b) = (1 + a / b)⁻¹ := by
        have h1 : (1 + a / b) = (a + b) / b := by field_simp; ring
        rw [h1, inv_div]
      rw [hKdef, hbase, Real.inv_rpow hypos.le, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos a) hpos_pow).mpr hpow_final
    have hCa : C / a ≤ (Real.exp 1 * (a + b) / a) ^ a := by
      have hx0powpos : 0 < x0 ^ a := Real.rpow_pos_of_pos hx0pos _
      have hle' : C * K * x0 ^ a ≤ a := by
        simpa using (div_le_iff₀ ha).mp hle_real
      have hstep1 : C / a ≤ 1 / (K * x0 ^ a) := by
        rw [div_le_iff₀ ha]
        have h2 : C ≤ a / (K * x0 ^ a) := by
          rw [le_div_iff₀ (mul_pos hKpos hx0powpos)]
          calc C * (K * x0 ^ a) = C * K * x0 ^ a := by ring
            _ ≤ a := hle'
        calc C ≤ a / (K * x0 ^ a) := h2
          _ = (1 / (K * x0 ^ a)) * a := by ring
      have hstep2 : 1 / (K * x0 ^ a) ≤ Real.exp a / x0 ^ a := by
        have h1 : Real.exp (-a) * x0 ^ a ≤ K * x0 ^ a :=
          mul_le_mul_of_nonneg_right hKexp hx0powpos.le
        have h2 : 0 < Real.exp (-a) * x0 ^ a := mul_pos (Real.exp_pos _) hx0powpos
        calc 1 / (K * x0 ^ a) ≤ 1 / (Real.exp (-a) * x0 ^ a) :=
              one_div_le_one_div_of_le h2 h1
          _ = Real.exp a / x0 ^ a := by
              rw [Real.exp_neg]
              field_simp
      have hstep3 : Real.exp a / x0 ^ a = (Real.exp 1 * (a + b) / a) ^ a := by
        rw [show Real.exp a = (Real.exp 1) ^ a by rw [Real.exp_one_rpow]]
        rw [← Real.div_rpow (Real.exp_pos 1).le hx0pos.le a]
        congr 1
        rw [hx0def]
        field_simp
      exact hstep1.trans (hstep2.trans hstep3.le)
    calc betaMeasure a b (Set.Iic t)
        ≤ ∫⁻ x in Set.Ioo 0 t, ENNReal.ofReal (C * x ^ (a - 1)) := by
            rw [hstep, hsupp]
            exact hle1
      _ = ENNReal.ofReal (C * t ^ a / a) := hInt
      _ ≤ ENNReal.ofReal ((Real.exp 1 * (a + b) * t / a) ^ a) := by
            apply ENNReal.ofReal_le_ofReal
            have h1 : C * t ^ a / a = (C / a) * t ^ a := by ring
            rw [h1]
            calc (C / a) * t ^ a ≤ ((Real.exp 1 * (a + b) / a) ^ a) * t ^ a :=
                  mul_le_mul_of_nonneg_right hCa (Real.rpow_nonneg ht0 _)
              _ = (Real.exp 1 * (a + b) * t / a) ^ a := by
                  rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ Real.exp 1 * (a + b) / a) ht0]
                  congr 1
                  ring
  · -- Case b < 1
    have hb_lt_one : b < 1 := lt_of_not_ge hb1
    have hle1 : ∫⁻ x in Set.Ioc 0 t, betaPDF a b x ≤
        ∫⁻ x in Set.Ioo 0 t, ENNReal.ofReal (C * x ^ (a - 1) * (1 - x / t) ^ (b - 1)) := by
      rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_mono_ae
      filter_upwards [hae_ne] with x hxt
      by_cases hx : x ∈ Set.Ioc 0 t
      · rw [Set.indicator_of_mem hx]
        by_cases hx' : x ∈ Set.Ioo 0 t
        · rw [Set.indicator_of_mem hx']
          rw [hPDFval x hx'.1 (hx'.2.trans_le ht1)]
          apply ENNReal.ofReal_le_ofReal
          have hbase_pos : 0 < 1 - x / t := by
            rw [sub_pos]
            exact (div_lt_one htpos).mpr hx'.2
          have hbase_le : 1 - x / t ≤ 1 - x := by
            have hxle : x ≤ x / t := by
              rw [le_div_iff₀ htpos]
              nlinarith [hx'.1.le, ht1]
            linarith
          have hpow : (1 - x) ^ (b - 1) ≤ (1 - x / t) ^ (b - 1) :=
            Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith : b - 1 ≤ 0)
          calc C * x ^ (a - 1) * (1 - x) ^ (b - 1)
              = (C * x ^ (a - 1)) * (1 - x) ^ (b - 1) := by ring
            _ ≤ (C * x ^ (a - 1)) * (1 - x / t) ^ (b - 1) :=
                mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnonneg (Real.rpow_nonneg hx'.1.le _))
            _ = C * x ^ (a - 1) * (1 - x / t) ^ (b - 1) := by ring
        · exfalso
          have hxt' : x = t := by
            rcases hx with ⟨hx0, hxtle⟩
            exact le_antisymm hxtle (le_of_not_gt fun h => hx' ⟨hx0, h⟩)
          exact hxt hxt'
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    -- scaling x = t*u
    have hscale : ∫⁻ x in Set.Ioo 0 t,
        ENNReal.ofReal (C * x ^ (a - 1) * (1 - x / t) ^ (b - 1)) =
        ENNReal.ofReal t * ∫⁻ u in Set.Ioo 0 1,
          ENNReal.ofReal (C * (t * u) ^ (a - 1) * (1 - (t * u) / t) ^ (b - 1)) := by
      have hmap : (volume : Measure ℝ) =
          ENNReal.ofReal t • Measure.map (fun u : ℝ => t * u) volume := by
        conv_lhs => rw [← Real.smul_map_volume_mul_left htpos.ne']
        rw [abs_of_pos htpos]
      rw [← lintegral_indicator measurableSet_Ioo]
      conv_lhs => rw [hmap]
      rw [lintegral_smul_measure]
      congr 1
      have hmeas_inner : Measurable (fun x : ℝ => C * x ^ (a - 1) * (1 - x / t) ^ (b - 1)) := by
        have hm_rpow : Measurable (fun x : ℝ => x ^ (a - 1)) :=
          measurable_of_continuousOn_compl_singleton 0 fun x hx =>
            (Real.continuousAt_rpow_const x (a - 1) (Or.inl hx)).continuousWithinAt
        have hm_rpow_b : Measurable (fun y : ℝ => y ^ (b - 1)) :=
          measurable_of_continuousOn_compl_singleton 0 fun y hy =>
            (Real.continuousAt_rpow_const y (b - 1) (Or.inl hy)).continuousWithinAt
        have hm2 : Measurable (fun x : ℝ => (1 - x / t) ^ (b - 1)) :=
          hm_rpow_b.comp (measurable_const.sub (measurable_id.div_const t))
        exact (hm_rpow.const_mul C).mul hm2
      rw [lintegral_map
        (f := (Set.Ioo 0 t).indicator
          (fun x : ℝ => ENNReal.ofReal (C * x ^ (a - 1) * (1 - x / t) ^ (b - 1))))
        (Measurable.indicator (measurable_ofReal.comp hmeas_inner) measurableSet_Ioo)
        (measurable_const_mul t)]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Set.Ioo 0 1
      · have hu' : t * u ∈ Set.Ioo 0 t :=
          ⟨mul_pos htpos hu.1, by nlinarith [hu.2, htpos]⟩
        rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu]
      · have hu' : t * u ∉ Set.Ioo 0 t := by
          intro h
          exact hu ⟨by nlinarith [h.1, htpos], by nlinarith [h.2, htpos]⟩
        rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hu]
    -- the density on (0,1) is normalized
    have hp : ∫⁻ u in Set.Ioo 0 1,
        ENNReal.ofReal (C * u ^ (a - 1) * (1 - u) ^ (b - 1)) = 1 := by
      rw [← hnorm]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact (hPDFval u hu.1 hu.2).symm
    have hgu : ∫⁻ u in Set.Ioo 0 1,
        ENNReal.ofReal (C * (t * u) ^ (a - 1) * (1 - (t * u) / t) ^ (b - 1)) =
        ENNReal.ofReal (t ^ (a - 1)) := by
      have hcongr1 : ∀ u ∈ Set.Ioo 0 1,
          ENNReal.ofReal (C * (t * u) ^ (a - 1) * (1 - (t * u) / t) ^ (b - 1)) =
          ENNReal.ofReal (C * (t ^ (a - 1) * u ^ (a - 1)) * (1 - u) ^ (b - 1)) := by
        intro u hu
        have hdiv : (t * u) / t = u := by field_simp
        rw [hdiv, Real.mul_rpow htpos.le hu.1.le]
      rw [setLIntegral_congr_fun measurableSet_Ioo hcongr1]
      have hcongr2 : ∀ u ∈ Set.Ioo 0 1,
          ENNReal.ofReal (C * (t ^ (a - 1) * u ^ (a - 1)) * (1 - u) ^ (b - 1)) =
          ENNReal.ofReal (t ^ (a - 1)) *
            ENNReal.ofReal (C * u ^ (a - 1) * (1 - u) ^ (b - 1)) := by
        intro u hu
        rw [show C * (t ^ (a - 1) * u ^ (a - 1)) * (1 - u) ^ (b - 1)
            = t ^ (a - 1) * (C * u ^ (a - 1) * (1 - u) ^ (b - 1)) by ring]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg htpos.le _)]
      rw [setLIntegral_congr_fun measurableSet_Ioo hcongr2]
      calc ∫⁻ u in Set.Ioo 0 1,
            ENNReal.ofReal (t ^ (a - 1)) *
              ENNReal.ofReal (C * u ^ (a - 1) * (1 - u) ^ (b - 1))
          = ENNReal.ofReal (t ^ (a - 1)) *
              ∫⁻ u in Set.Ioo 0 1, ENNReal.ofReal (C * u ^ (a - 1) * (1 - u) ^ (b - 1)) :=
              lintegral_const_mul (ENNReal.ofReal (t ^ (a - 1)))
                (measurable_ofReal.comp (by measurability) :
                  Measurable (fun u : ℝ => ENNReal.ofReal (C * u ^ (a - 1) * (1 - u) ^ (b - 1))))
        _ = ENNReal.ofReal (t ^ (a - 1)) * 1 := by rw [hp]
        _ = ENNReal.ofReal (t ^ (a - 1)) := mul_one _
    have hInt : ∫⁻ x in Set.Ioo 0 t,
        ENNReal.ofReal (C * x ^ (a - 1) * (1 - x / t) ^ (b - 1)) =
        ENNReal.ofReal (t ^ a) := by
      rw [hscale, hgu, ← ENNReal.ofReal_mul ht0]
      congr 1
      calc t * t ^ (a - 1) = t ^ 1 * t ^ (a - 1) := by rw [Real.rpow_one]
        _ = t ^ (1 + (a - 1)) := (Real.rpow_add htpos 1 (a - 1)).symm
        _ = t ^ a := by rw [show 1 + (a - 1) = a by ring]
    calc betaMeasure a b (Set.Iic t)
        ≤ ∫⁻ x in Set.Ioo 0 t,
            ENNReal.ofReal (C * x ^ (a - 1) * (1 - x / t) ^ (b - 1)) := by
            rw [hstep, hsupp]
            exact hle1
      _ = ENNReal.ofReal (t ^ a) := hInt
      _ ≤ ENNReal.ofReal ((Real.exp 1 * (a + b) * t / a) ^ a) := by
            apply ENNReal.ofReal_le_ofReal
            have hge1 : 1 ≤ Real.exp 1 * (a + b) / a := by
              have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
              have h2 : 1 ≤ (a + b) / a := by
                rw [le_div_iff₀ ha]
                linarith
              calc 1 = 1 * 1 := by ring
                _ ≤ Real.exp 1 * ((a + b) / a) :=
                    mul_le_mul h1 h2 (by norm_num) (Real.exp_pos 1).le
                _ = Real.exp 1 * (a + b) / a := by ring
            calc t ^ a ≤ ((Real.exp 1 * (a + b) / a) * t) ^ a := by
                  apply Real.rpow_le_rpow ht0
                  · exact le_mul_of_one_le_left ht0 hge1
                  · exact ha.le
              _ = (Real.exp 1 * (a + b) * t / a) ^ a := by
                  rw [show (Real.exp 1 * (a + b) / a) * t = Real.exp 1 * (a + b) * t / a by ring]

