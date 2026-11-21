-- Prove2me | solution 1 for MarketInterference.FluidLimit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:07:30.5861+00:00
-- url     : https://prove2.me/submissions/e754f0cd-22da-4607-b4b3-50c24f173ff2

import Mathlib

open MeasureTheory ProbabilityTheory NNReal ENNReal

set_option maxHeartbeats 8000000

lemma poisson_lintegral_exp (r : ℝ≥0) (s : ℝ) :
    ∫⁻ k : ℕ, ENNReal.ofReal (Real.exp (s * (k : ℝ))) ∂poissonMeasure r
      = ENNReal.ofReal (Real.exp ((r : ℝ) * (Real.exp s - 1))) := by
  have hexp_pow : ∀ k : ℕ, Real.exp s ^ k = Real.exp (s * (k : ℝ)) := by
    intro k
    rw [← Real.exp_nat_mul]
    ring_nf
  have hS : Summable (fun k : ℕ =>
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * Real.exp (s * (k : ℝ))) := by
    have hbase : Summable (fun k : ℕ =>
        Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp s) ^ k / (k.factorial : ℝ))) :=
      (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp s)).summable.mul_left _
    refine hbase.congr (fun k => ?_)
    simp only [mul_pow, hexp_pow k]
    ring
  have hint : Integrable (fun k : ℕ => Real.exp (s * (k : ℝ))) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine hS.congr (fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun k => (Real.exp_pos _).le))]
  congr 1
  rw [integral_poissonMeasure r (fun k => Real.exp (s * (k : ℝ)))]
  simp only [smul_eq_mul]
  have htsum : (∑' k : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) *
      Real.exp (s * (k : ℝ)))
      = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp s) := by
    have hterm : ∀ k : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) *
        Real.exp (s * (k : ℝ))
        = Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp s) ^ k / (k.factorial : ℝ)) := by
      intro k
      simp only [mul_pow, hexp_pow k]
      ring
    simp only [hterm]
    rw [_root_.tsum_mul_left]
    congr 1
    have hsum := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp s)).tsum_eq
    rw [← Real.exp_eq_exp_ℝ] at hsum
    exact hsum
  rw [htsum]
  rw [← Real.exp_add]
  congr 1
  ring

lemma poisson_tail_le (r : ℝ≥0) (s : ℝ) (hs : 0 < s) (m : ℕ) :
    poissonMeasure r (Set.Ici m) ≤
      ENNReal.ofReal (Real.exp ((r : ℝ) * (Real.exp s - 1) - s * (m : ℝ))) := by
  have hf : Measurable (fun k : ℕ => ENNReal.ofReal (Real.exp (s * (k : ℝ)))) :=
    Measurable.of_discrete.ennreal_ofReal
  have hmarkov := mul_meas_ge_le_lintegral (μ := poissonMeasure r) hf
    (ENNReal.ofReal (Real.exp (s * (m : ℝ))))
  have hset : {k : ℕ | ENNReal.ofReal (Real.exp (s * (m : ℝ))) ≤
      ENNReal.ofReal (Real.exp (s * (k : ℝ)))} = Set.Ici m := by
    ext k
    rw [Set.mem_setOf_eq, Set.mem_Ici, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp, mul_le_mul_iff_of_pos_left hs, Nat.cast_le]
  rw [hset] at hmarkov
  rw [poisson_lintegral_exp r s] at hmarkov
  have hdiv : poissonMeasure r (Set.Ici m) ≤
      ENNReal.ofReal (Real.exp ((r : ℝ) * (Real.exp s - 1))) /
        ENNReal.ofReal (Real.exp (s * (m : ℝ))) := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
      (Or.inl ENNReal.ofReal_ne_top)]
    rw [mul_comm]
    exact hmarkov
  refine le_trans hdiv ?_
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_sub]

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (X : ℕ → Ω → ℕ)
    (hX : ∀ n : ℕ, 1 ≤ n → Measurable (X n) ∧ P.map (X n) = poissonMeasure ((n : ℝ≥0) * lam)) :
    ∫⁻ ω, (⨆ (n : ℕ) (_ : 1 ≤ n), ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ))) ∂P < ⊤ := by
  classical
  set Z : Ω → ℝ≥0∞ := fun ω =>
    ⨆ (n : ℕ) (_ : 1 ≤ n), ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ)) with hZdef
  set T : ℝ := max 4 (Real.exp ((lam : ℝ) + 2)) with hTdef
  have hT4 : (4 : ℝ) ≤ T := le_max_left _ _
  have hTexp : Real.exp ((lam : ℝ) + 2) ≤ T := le_max_right _ _
  have hTpos : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) < T := by linarith
  -- measurability of Z
  have hZmeas : Measurable Z := by
    rw [hZdef]
    refine Measurable.iSup (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simpa using measurable_const (a := (0 : ℝ≥0∞))
    · have hcast : Measurable fun ω => (X n ω : ℝ) :=
        (measurable_of_countable (fun x : ℕ => (x : ℝ))).comp ((hX n hn).1)
      exact Measurable.iSup_Prop _ (hcast.div_const _).ennreal_ofReal
  -- one-step Chernoff bound for each n
  have hstep : ∀ (n : ℕ), 1 ≤ n → ∀ u : ℝ, 1 < u →
      P {ω | ENNReal.ofReal u < ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ))} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (u * Real.log u - (lam : ℝ) * (u - 1)))) := by
    intro n hn u hu
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hu0 : (0 : ℝ) < u := by linarith
    have hset1 : {ω | ENNReal.ofReal u < ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ))}
        = {ω | u < (X n ω : ℝ) / (n : ℝ)} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (X n ω : ℝ) / (n : ℝ)) with h | h
      · rw [← h, ENNReal.ofReal_zero]
        exact iff_of_false (not_lt.mpr (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal u)) (by linarith)
      · exact ENNReal.ofReal_lt_ofReal_iff h
    rw [hset1]
    set m : ℕ := ⌊u * (n : ℝ)⌋₊ + 1 with hm
    have hset2 : {ω | u < (X n ω : ℝ) / (n : ℝ)} = {ω | m ≤ X n ω} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, lt_div_iff₀ hnpos]
      have h1 : (0 : ℝ) ≤ u * (n : ℝ) := by positivity
      constructor
      · intro h
        have h2 : ⌊u * (n : ℝ)⌋₊ < X n ω := (Nat.floor_lt h1).mpr h
        omega
      · intro h
        have h2 : ⌊u * (n : ℝ)⌋₊ < X n ω := by omega
        exact (Nat.floor_lt h1).mp h2
    rw [hset2]
    have hmap : P (X n ⁻¹' Set.Ici m) = poissonMeasure ((n : ℝ≥0) * lam) (Set.Ici m) := by
      rw [← Measure.map_apply (hX n hn).1 measurableSet_Ici, (hX n hn).2]
    have hpre : X n ⁻¹' Set.Ici m = {ω | m ≤ X n ω} := rfl
    rw [← hpre, hmap]
    have hs : (0 : ℝ) < Real.log u := Real.log_pos hu
    refine le_trans (poisson_tail_le ((n : ℝ≥0) * lam) (Real.log u) hs m) ?_
    apply ENNReal.ofReal_le_ofReal
    have hexplog : Real.exp (Real.log u) = u := Real.exp_log hu0
    have hmn : u * (n : ℝ) ≤ (m : ℝ) := by
      have h := Nat.lt_floor_add_one (u * (n : ℝ))
      rw [hm]; push_cast; linarith
    have hcast : (((n : ℝ≥0) * lam : ℝ≥0) : ℝ) = (n : ℝ) * (lam : ℝ) := by push_cast; ring
    rw [hcast, hexplog]
    apply Real.exp_le_exp.mpr
    have hprod : Real.log u * (u * (n : ℝ)) ≤ Real.log u * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hmn hs.le
    nlinarith [hprod]
  -- tail bound above T
  have htail : ∀ u : ℝ, T ≤ u →
      P {ω | ENNReal.ofReal u < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-(u / 2))) := by
    intro u huT
    have hu1 : 1 < u := by linarith
    have hu0 : 0 < u := by linarith
    have hlog : (lam : ℝ) + 2 ≤ Real.log u := by
      have h1 : Real.log (Real.exp ((lam : ℝ) + 2)) ≤ Real.log u :=
        Real.log_le_log (Real.exp_pos _) (le_trans hTexp huT)
      rwa [Real.log_exp] at h1
    set c : ℝ := u * Real.log u - (lam : ℝ) * (u - 1) with hc
    have hc_ge : u / 2 ≤ c := by
      rw [hc]; nlinarith [hlog, hu0]
    have hc1 : (1 : ℝ) ≤ c := by linarith
    -- union bound indexed by k = n - 1
    have hsub : {ω | ENNReal.ofReal u < Z ω} ⊆
        ⋃ k : ℕ, {ω | ENNReal.ofReal u <
          ENNReal.ofReal ((X (k + 1) ω : ℝ) / ((k + 1 : ℕ) : ℝ))} := by
      intro ω hω
      have hω' : ENNReal.ofReal u < Z ω := hω
      rw [hZdef] at hω'
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hω'
      obtain ⟨hn1, hn2⟩ := lt_iSup_iff.mp hn
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact Set.mem_iUnion.mpr ⟨k, by rwa [hk] at hn2⟩
    have hterm : ∀ k : ℕ, P {ω | ENNReal.ofReal u <
        ENNReal.ofReal ((X (k + 1) ω : ℝ) / ((k + 1 : ℕ) : ℝ))} ≤
        ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * c))) := by
      intro k
      have h := hstep (k + 1) (Nat.le_add_left 1 k) u hu1
      have hc' : u * Real.log u - (lam : ℝ) * (u - 1) = c := by rw [hc]
      rw [hc'] at h
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hgoal : -(((k : ℝ) + 1) * c) = (-1 + -(k : ℝ)) * c := by ring
      rw [hgoal]
      simpa [hcast] using h
    have hgeom : (∑' k : ℕ, ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * c)))) ≤
        ENNReal.ofReal (2 * Real.exp (-c)) := by
      have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
      have hr1 : Real.exp (-c) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hsumm : Summable (fun k : ℕ => Real.exp (-(((k : ℝ) + 1) * c))) := by
        have hr2 : Real.exp (-c) < 1 := hr1
        have heq : ∀ k : ℕ, Real.exp (-(((k : ℝ) + 1) * c)) =
            Real.exp (-c) * (Real.exp (-c)) ^ k := by
          intro k
          rw [show -(((k : ℝ) + 1) * c) = (((k + 1 : ℕ)) : ℝ) * (-c) by push_cast; ring,
            Real.exp_nat_mul, pow_succ]
          ring
        simp only [heq]
        exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
      have hval : (∑' k : ℕ, Real.exp (-(((k : ℝ) + 1) * c))) ≤ 2 * Real.exp (-c) := by
        have heq : ∀ k : ℕ, Real.exp (-(((k : ℝ) + 1) * c)) =
            Real.exp (-c) * (Real.exp (-c)) ^ k := by
          intro k
          rw [show -(((k : ℝ) + 1) * c) = (((k + 1 : ℕ)) : ℝ) * (-c) by push_cast; ring,
            Real.exp_nat_mul, pow_succ]
          ring
        simp only [heq]
        rw [_root_.tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        have hhalf : Real.exp (-c) ≤ 1 / 2 := by
          have h5 : Real.exp (-c) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
          have h6 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
            have h7 : (2 : ℝ) ≤ Real.exp 1 := by
              have h8 := Real.add_one_le_exp (1 : ℝ)
              linarith [Real.exp_pos (1 : ℝ)]
            rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos 1)]
            nlinarith
          linarith
        have hpos : 0 < 1 - Real.exp (-c) := by linarith
        have h9 : (1 - Real.exp (-c))⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ hpos]
          linarith
        nlinarith [Real.exp_pos (-c)]
      calc (∑' k : ℕ, ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * c))))
          = ENNReal.ofReal (∑' k : ℕ, Real.exp (-(((k : ℝ) + 1) * c))) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsumm).symm
        _ ≤ ENNReal.ofReal (2 * Real.exp (-c)) := ENNReal.ofReal_le_ofReal hval
    calc P {ω | ENNReal.ofReal u < Z ω}
        ≤ P (⋃ k : ℕ, {ω | ENNReal.ofReal u <
            ENNReal.ofReal ((X (k + 1) ω : ℝ) / ((k + 1 : ℕ) : ℝ))}) := measure_mono hsub
      _ ≤ ∑' k : ℕ, P {ω | ENNReal.ofReal u <
            ENNReal.ofReal ((X (k + 1) ω : ℝ) / ((k + 1 : ℕ) : ℝ))} := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * c))) :=
          ENNReal.tsum_le_tsum hterm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c)) := hgeom
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(u / 2))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  -- sup of truncations
  have hmin_sup : ∀ z : ℝ≥0∞, (⨆ N : ℕ, min z (N : ℝ≥0∞)) = z := by
    intro z
    refine le_antisymm (iSup_le (fun N => min_le_left _ _)) ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hbz, hb⟩ := iSup_lt_iff.mp hlt
    have hbfin : b ≠ ∞ := ne_top_of_lt hbz
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hbfin
    have h1 : b < min z (N : ℝ≥0∞) := lt_min hbz (by exact_mod_cast hN)
    exact absurd (hb N) (not_le.mpr h1)
  -- final bound
  have hfin : ∫⁻ ω, Z ω ∂P ≤ ENNReal.ofReal (T + 4) := by
    have hZeq : Z = fun ω => ⨆ N : ℕ, min (Z ω) (N : ℝ≥0∞) := by
      funext ω
      exact (hmin_sup (Z ω)).symm
    rw [hZeq, lintegral_iSup (fun N => hZmeas.min measurable_const) ?_]
    · refine iSup_le (fun N => ?_)
      have h1 : ∫⁻ ω, min (Z ω) (N : ℝ≥0∞) ∂P =
          ∫⁻ t in Set.Ioi 0, P {a | t < (min (Z a) (N : ℝ≥0∞)).toReal} := by
        rw [← lintegral_eq_lintegral_meas_lt P
          (f := fun ω => (min (Z ω) (N : ℝ≥0∞)).toReal)
          (Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg))
          ((hZmeas.min measurable_const).aemeasurable.ennreal_toReal)]
        refine lintegral_congr (fun ω => ?_)
        exact (ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (min_le_right _ _)
          ENNReal.coe_lt_top))).symm
      rw [h1]
      have hpt : ∀ t : ℝ, P {a | t < (min (Z a) (N : ℝ≥0∞)).toReal} ≤
          ENNReal.ofReal (if t ≤ T then 1 else 2 * Real.exp (-(t / 2))) := by
        intro t
        by_cases htT : t ≤ T
        · rw [if_pos htT, ENNReal.ofReal_one]
          calc P {a | t < (min (Z a) (N : ℝ≥0∞)).toReal} ≤ P Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        · rw [if_neg htT]
          have ht0 : 0 < t := by linarith
          have hsub2 : {a | t < (min (Z a) (N : ℝ≥0∞)).toReal} ⊆
              {a | ENNReal.ofReal t < Z a} := by
            intro a ha
            have h1 : 0 < (min (Z a) (N : ℝ≥0∞)).toReal := lt_trans ht0 ha
            have h2 : ENNReal.ofReal t < ENNReal.ofReal ((min (Z a) (N : ℝ≥0∞)).toReal) :=
              (ENNReal.ofReal_lt_ofReal_iff h1).mpr ha
            have h3 : ENNReal.ofReal ((min (Z a) (N : ℝ≥0∞)).toReal) = min (Z a) (N : ℝ≥0∞) :=
              ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (min_le_right _ _)
                ENNReal.coe_lt_top))
            rw [h3] at h2
            exact lt_of_lt_of_le h2 (min_le_left _ _)
          exact le_trans (measure_mono hsub2) (htail t (le_of_lt (lt_of_not_ge htT)))
      calc ∫⁻ t in Set.Ioi 0, P {a | t < (min (Z a) (N : ℝ≥0∞)).toReal}
          ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (if t ≤ T then 1 else 2 * Real.exp (-(t / 2))) :=
            lintegral_mono hpt
        _ ≤ ∫⁻ t in Set.Ioi 0, ((Set.Ioc 0 T).indicator (1 : ℝ → ℝ≥0∞) t +
              ENNReal.ofReal (2 * Real.exp (-(t / 2)))) := by
            refine lintegral_mono (fun t => ?_)
            by_cases htT : t ≤ T
            · rw [if_pos htT, ENNReal.ofReal_one]
              by_cases ht0 : 0 < t
              · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 T from ⟨ht0, htT⟩), Pi.one_apply]
                simp
              · rw [Set.indicator_of_notMem (by simp [ht0]), zero_add]
                rw [ENNReal.one_le_ofReal]
                have : (1 : ℝ) ≤ Real.exp (-(t / 2)) := by
                  rw [← Real.exp_zero]
                  exact Real.exp_le_exp.mpr (by linarith)
                nlinarith
            · rw [if_neg htT]
              rw [Set.indicator_of_notMem (by simp [htT]), zero_add]
        _ = (∫⁻ t in Set.Ioi 0, (Set.Ioc 0 T).indicator (1 : ℝ → ℝ≥0∞) t) +
              ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (2 * Real.exp (-(t / 2))) := by
            change ∫⁻ t, (Set.Ioc 0 T).indicator (1 : ℝ → ℝ≥0∞) t +
              ENNReal.ofReal (2 * Real.exp (-(t / 2))) ∂(volume.restrict (Set.Ioi 0)) =
              (∫⁻ t in Set.Ioi 0, (Set.Ioc 0 T).indicator (1 : ℝ → ℝ≥0∞) t) +
              ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (2 * Real.exp (-(t / 2)))
            exact lintegral_add_left (measurable_const.indicator measurableSet_Ioc) _
        _ ≤ ENNReal.ofReal T + ENNReal.ofReal 4 := by
            apply add_le_add
            · rw [lintegral_indicator_one measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
                Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Real.volume_Ioc]
              simp
            · have hfun : ∀ t : ℝ, ENNReal.ofReal (2 * Real.exp (-(t / 2)))
                  = ENNReal.ofReal (2 * Real.exp (-((1 / 2) * t))) := by
                intro t
                rw [show -(t / 2) = -((1 / 2) * t) by ring]
              simp_rw [hfun]
              rw [← ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioi 0))
                (f := fun t : ℝ => 2 * Real.exp (-((1 / 2) * t)))
                (by
                  have h := (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
                  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
                  congr 2
                  ring)
                (Filter.Eventually.of_forall (fun t => by positivity))]
              apply ENNReal.ofReal_le_ofReal
              rw [integral_const_mul]
              have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / 2)
                one_pos (by norm_num)
              simp only [sub_self, Real.rpow_zero, one_mul] at h
              have h5 : (1 / (1 / 2) : ℝ) ^ (1 : ℝ) * Real.Gamma 1 = 2 := by
                have h6 : (1 / (1 / 2) : ℝ) = 2 := by norm_num
                rw [h6, Real.rpow_one, Real.Gamma_one]
                norm_num
              have h2 : (∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(1 / 2 * t))) = 2 := by
                calc (∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(1 / 2 * t)))
                    = (1 / (1 / 2) : ℝ) ^ (1 : ℝ) * Real.Gamma 1 := by
                      rw [← h]
                  _ = 2 := h5
              rw [h2]
              norm_num
        _ = ENNReal.ofReal (T + 4) := by
            rw [ENNReal.ofReal_add (by linarith) (by norm_num)]
    · intro a b hab ω
      exact min_le_min le_rfl (by exact_mod_cast hab)
  calc ∫⁻ ω, (⨆ (n : ℕ) (_ : 1 ≤ n), ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ))) ∂P
      = ∫⁻ ω, Z ω ∂P := by rw [hZdef]
    _ ≤ ENNReal.ofReal (T + 4) := hfin
    _ < ⊤ := ENNReal.ofReal_lt_top
