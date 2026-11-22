-- Prove2me | solution 1 for Kyprianou.Ch01.mg1IdleLight
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:41:10.203817+00:00
-- url     : https://prove2.me/submissions/d973b1d7-4ba8-4ad0-8dc9-8612b3cd7c42

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_mg1IdleRegulatorIdentity
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Function
open scoped NNReal ENNReal Topology
set_option autoImplicit false
universe u

private lemma integrable_id_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hlt : ∀ᵐ x ∂volume, gammaPDF 1 r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff hmeas hlt]
  have hEq : (fun x : ℝ => x * (gammaPDF 1 r x).toReal) =
      (Set.Ici (0 : ℝ)).indicator (fun x : ℝ => r * (x * Real.exp (-(r * x)))) := by
    ext x
    by_cases hx : 0 ≤ x
    · have hmem : x ∈ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_mem hmem]
      simp only [gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      ring
    · have hlt' : x < 0 := lt_of_not_ge hx
      have hnm : x ∉ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hnm, gammaPDF_of_neg hlt']
      simp
  rw [hEq, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have hDom : IntegrableOn (fun x : ℝ => (2 : ℝ) * Real.exp (-(r / 2) * x)) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul 2
  refine hDom.mono' ?_ ?_
  · exact (measurable_const.mul (measurable_id.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id).neg))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (r / 2) * x ≤ Real.exp ((r / 2) * x) := by
      linarith [Real.add_one_le_exp ((r / 2) * x)]
    have h2 : r * x * Real.exp (-(r * x)) ≤ 2 * Real.exp (-(r / 2) * x) := by
      have hmul : 2 * ((r / 2) * x) * Real.exp (-(r * x)) ≤
          2 * Real.exp ((r / 2) * x) * Real.exp (-(r * x)) := by
        gcongr
      calc r * x * Real.exp (-(r * x))
          = 2 * ((r / 2) * x) * Real.exp (-(r * x)) := by ring
        _ ≤ 2 * Real.exp ((r / 2) * x) * Real.exp (-(r * x)) := hmul
        _ = 2 * (Real.exp ((r / 2) * x) * Real.exp (-(r * x))) := by ring
        _ = 2 * Real.exp ((r / 2) * x + -(r * x)) := by rw [← Real.exp_add]
        _ = 2 * Real.exp (-(r / 2) * x) := by congr 2; ring
    linarith

private lemma integral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, x ∂(expMeasure r)) = r⁻¹ := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hlt : ∀ᵐ x ∂volume, gammaPDF 1 r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have hEq : (fun x : ℝ => (gammaPDF 1 r x).toReal • x) =
      (Set.Ici (0 : ℝ)).indicator (fun x : ℝ => r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)))) := by
    ext x
    by_cases hx : 0 ≤ x
    · have hmem : x ∈ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_mem hmem]
      simp only [smul_eq_mul, gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one,
        div_one, sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      have h21 : (2 : ℝ) - 1 = 1 := by norm_num
      rw [h21, Real.rpow_one]
      ring
    · have hlt' : x < 0 := lt_of_not_ge hx
      have hnm : x ∉ Set.Ici (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hnm, gammaPDF_of_neg hlt']
      simp
  rw [hEq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hInt : (∫ x in Set.Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)) ∂volume) =
      r ^ (-(2 : ℝ)) * Real.Gamma 2 := by
    simpa [neg_mul] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) hr)
  rw [hInt]
  have hG2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    simp
  rw [hG2]
  have hrne : r ≠ 0 := hr.ne'
  rw [show r ^ (-(2 : ℝ)) = (r ^ (2 : ℕ))⁻¹ by
    rw [Real.rpow_neg hr.le]
    norm_cast]
  field_simp [hrne]

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hlight : (rate : ℝ) * mu < 1) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1 := by
  intro w hw
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  -- 1. SLLN for interarrival times
  have hArr_int : Integrable (arrival 0) P := by
    have hlaw := hd.law_interarrival 0
    have h1 := integrable_id_expMeasure hrateR
    rw [← hlaw.map_eq] at h1
    exact h1.comp_aemeasurable (hd.measurable_interarrival 0).aemeasurable
  have hArr_mean : (∫ ω, arrival 0 ω ∂P) = (rate : ℝ)⁻¹ := by
    have hlaw := hd.law_interarrival 0
    have h1 := integral_id_expMeasure hrateR
    rw [← hlaw.map_eq] at h1
    have h2 : (∫ y : ℝ, y ∂(P.map (arrival 0))) = ∫ ω, arrival 0 ω ∂P :=
      integral_map (hd.measurable_interarrival 0).aemeasurable
        (aestronglyMeasurable_id (μ := P.map (arrival 0)))
    exact h2.symm.trans h1
  have hArr_indep : Pairwise ((· ⟂ᵢ[P] ·) on arrival) := by
    intro i j hij
    have hi : iIndepFun (fun k => Sum.elim arrival claims (Sum.inl k)) P :=
      hd.indep.precomp Sum.inl_injective
    exact hi.indepFun hij
  have hArr_ident : ∀ i : ℕ, IdentDistrib (arrival i) (arrival 0) P P := fun i =>
    { aemeasurable_fst := (hd.measurable_interarrival i).aemeasurable
      aemeasurable_snd := (hd.measurable_interarrival 0).aemeasurable
      map_eq := by rw [(hd.law_interarrival i).map_eq, (hd.law_interarrival 0).map_eq] }
  have hArr_slln : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, arrival i ω) / (n : ℝ))
        atTop (𝓝 ((rate : ℝ)⁻¹)) := by
    simpa [hArr_mean] using strong_law_ae_real arrival hArr_int hArr_indep hArr_ident
  -- 2. SLLN for claim sizes
  have hClm_int : Integrable (claims 0) P := by
    have hlaw := hd.law_mark 0
    rw [← hlaw.map_eq] at hclaimint
    exact hclaimint.comp_aemeasurable (hd.measurable_mark 0).aemeasurable
  have hClm_mean : (∫ ω, claims 0 ω ∂P) = mu := by
    have hlaw := hd.law_mark 0
    rw [← hlaw.map_eq] at hmean
    have h2 : (∫ y : ℝ, y ∂(P.map (claims 0))) = ∫ ω, claims 0 ω ∂P :=
      integral_map (hd.measurable_mark 0).aemeasurable
        (aestronglyMeasurable_id (μ := P.map (claims 0)))
    exact h2.symm.trans hmean
  have hClm_indep : Pairwise ((· ⟂ᵢ[P] ·) on claims) := by
    intro i j hij
    have hi : iIndepFun (fun k => Sum.elim arrival claims (Sum.inr k)) P :=
      hd.indep.precomp Sum.inr_injective
    exact hi.indepFun hij
  have hClm_ident : ∀ i : ℕ, IdentDistrib (claims i) (claims 0) P P := fun i =>
    { aemeasurable_fst := (hd.measurable_mark i).aemeasurable
      aemeasurable_snd := (hd.measurable_mark 0).aemeasurable
      map_eq := by rw [(hd.law_mark i).map_eq, (hd.law_mark 0).map_eq] }
  have hClm_slln : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, claims i ω) / (n : ℝ))
        atTop (𝓝 mu) := by
    simpa [hClm_mean] using strong_law_ae_real claims hClm_int hClm_indep hClm_ident
  -- 3. Combine with regulator identity and compound Poisson path properties
  have hReg := Kyprianou.Ch01.mg1IdleRegulatorIdentity P arrival claims rate hrate F hd hclaimpos w hw
  have hPos := hd.ae_interarrival_pos hrate
  have hStrict := hd.ae_strictMono_arrival hrate
  have hTendsto := hd.ae_tendsto_arrival hrate
  have hClaimsPos : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    have hlaw : P.map (claims n) = F := (hd.law_mark n).map_eq
    have hmeas : Measurable (claims n) := hd.measurable_mark n
    have hzero : P {ω | claims n ω ≤ 0} = 0 := by
      have hpre : {ω | claims n ω ≤ 0} = claims n ⁻¹' Set.Iic (0 : ℝ) := rfl
      rw [hpre, ← Measure.map_apply hmeas measurableSet_Iic, hlaw, hclaimpos]
    rw [ae_iff]
    convert hzero using 2
    ext ω
    simp [not_lt]
  have hAE_top : ∀ᵐ ω ∂P, totalIdleTime arrival claims w ω = ⊤ := by
    filter_upwards [hArr_slln, hClm_slln, hReg, hPos, hStrict, hTendsto, hClaimsPos] with
      ω hArrω hClmω hRegω hPosω hStrictω hTendstoω hClaimsω
    have hDrift : 0 < (rate : ℝ)⁻¹ - mu := by
      rw [sub_pos, ← mul_lt_mul_iff_right₀ hrateR, mul_inv_cancel₀ hrateR.ne']
      linarith
    have hDiff_tendsto :
        Tendsto (fun n : ℕ =>
          ((∑ i ∈ Finset.range n, arrival i ω) - (∑ i ∈ Finset.range n, claims i ω)) / (n : ℝ))
          atTop (𝓝 ((rate : ℝ)⁻¹ - mu)) := by
      have hSub := hArrω.sub hClmω
      refine hSub.congr fun n => ?_
      ring
    -- Show totalIdleTime ≥ ENNReal.ofReal M for all M : ℝ
    rw [eq_top_iff]
    refine le_of_forall_lt fun b hb => ?_
    -- Find M : ℝ such that b < ENNReal.ofReal M
    have hb_ne : b ≠ ⊤ := hb.ne
    set M : ℝ := b.toReal + 1
    have hb_lt : b < ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal hb_ne]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
    -- Pick n ≥ 1 large enough that X_{T_{n-1}} - w ≥ M
    have hEv : ∀ᶠ n : ℕ in atTop,
        ((rate : ℝ)⁻¹ - mu) / 2 <
          ((∑ i ∈ Finset.range n, arrival i ω) - (∑ i ∈ Finset.range n, claims i ω)) / (n : ℝ) :=
      hDiff_tendsto.eventually (lt_mem_nhds (by linarith))
    rw [Filter.eventually_atTop] at hEv
    obtain ⟨N0, hN0⟩ := hEv
    obtain ⟨N1, hN1⟩ := exists_nat_gt ((max M 0 + w) / (((rate : ℝ)⁻¹ - mu) / 2))
    set n : ℕ := max (max N0 N1) 1
    have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hn_ge_N0 : N0 ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
    have hn_ge_N1 : N1 ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
    have hRatio := hN0 n hn_ge_N0
    have hnR_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hSum_ge : M + w <
        (∑ i ∈ Finset.range n, arrival i ω) - (∑ i ∈ Finset.range n, claims i ω) := by
      have h1 : (n : ℝ) * (((rate : ℝ)⁻¹ - mu) / 2) <
          (∑ i ∈ Finset.range n, arrival i ω) - (∑ i ∈ Finset.range n, claims i ω) := by
        rwa [lt_div_iff₀ hnR_pos, mul_comm] at hRatio
      have h2 : (max M 0 + w) / (((rate : ℝ)⁻¹ - mu) / 2) < (n : ℝ) :=
        lt_of_lt_of_le hN1 (Nat.cast_le.mpr hn_ge_N1)
      have h3 : max M 0 + w < (n : ℝ) * (((rate : ℝ)⁻¹ - mu) / 2) := by
        rwa [div_lt_iff₀ (by linarith)] at h2
      have h4 : M ≤ max M 0 := le_max_left _ _
      linarith
    -- Evaluate at t_n = arrival (n - 1) ω
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel hn_pos
    set tR : ℝ := ProbabilityTheory.arrival arrival (n - 1) ω
    have htR_eq : tR = ∑ i ∈ Finset.range n, arrival i ω := by
      dsimp [tR, ProbabilityTheory.arrival]
      rw [hn_eq]
    have htR_nonneg : 0 ≤ tR := by
      rw [htR_eq]
      exact Finset.sum_nonneg fun i _ => (hPosω i).le
    set t : ℝ≥0 := ⟨tR, htR_nonneg⟩
    have hjc : jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) tR = n := by
      have hgt : n - 1 < jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) tR :=
        (lt_jumpCount_iff hStrictω hTendstoω (n - 1) tR).mpr le_rfl
      have hle : ¬ (n < jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) tR) := by
        rw [lt_jumpCount_iff hStrictω hTendstoω]
        have hlt : tR < ProbabilityTheory.arrival arrival n ω :=
          hStrictω (by omega : n - 1 < n)
        exact not_le.mpr hlt
      omega
    have hcoe : (t : ℝ) = tR := rfl
    have hSurplus_t : riskSurplus arrival claims 1 0 t ω =
        (∑ i ∈ Finset.range n, arrival i ω) - (∑ i ∈ Finset.range n, claims i ω) := by
      rw [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath, hcoe, hjc, htR_eq]
      ring
    have hBdd : BddAbove {x : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ x = riskSurplus arrival claims 1 0 s ω} := by
      refine ⟨(t : ℝ), ?_⟩
      rintro x ⟨s, hs, rfl⟩
      simp only [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath]
      have hsum_nn : 0 ≤ ∑ i ∈ Finset.range
          (jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) (s : ℝ)), claims i ω :=
        Finset.sum_nonneg fun i _ => (hClaimsω i).le
      have hst : (s : ℝ) ≤ (t : ℝ) := hs
      linarith
    have hSup_ge : riskSurplus arrival claims 1 0 t ω ≤
        sSup {x : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ x = riskSurplus arrival claims 1 0 s ω} :=
      le_csSup hBdd ⟨t, le_rfl, rfl⟩
    have hM_le_int : M ≤ ∫ s in (0 : ℝ)..(t : ℝ),
        (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
          then (1 : ℝ) else 0) ∂volume := by
      rw [hRegω t]
      refine le_trans ?_ (le_max_left _ _)
      linarith [hSurplus_t, hSup_ge]
    -- Compare interval integral to totalIdleTime
    have hInt_le_idle :
        ENNReal.ofReal (∫ s in (0 : ℝ)..(t : ℝ),
          (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
            then (1 : ℝ) else 0) ∂volume) ≤ totalIdleTime arrival claims w ω := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)]
      let f : ℝ → ℝ := fun s =>
        if queueWorkload arrival claims w (Real.toNNReal s) ω = 0 then (1 : ℝ) else 0
      by_cases hfInt : IntegrableOn f (Set.Ioc (0 : ℝ) (t : ℝ)) volume
      · calc ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ) (t : ℝ), f s ∂volume)
            = ∫⁻ s in Set.Ioc (0 : ℝ) (t : ℝ), ENNReal.ofReal (f s) ∂volume :=
              ofReal_integral_eq_lintegral_ofReal hfInt
                (Filter.Eventually.of_forall fun s => by dsimp [f]; split_ifs <;> positivity)
          _ = ∫⁻ s in Set.Ioc (0 : ℝ) (t : ℝ),
                (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
                  then (1 : ℝ≥0∞) else 0) ∂volume := by
              refine lintegral_congr fun s => ?_
              dsimp [f]; split_ifs <;> simp
          _ ≤ ∫⁻ s in Set.Ici (0 : ℝ),
                (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
                  then (1 : ℝ≥0∞) else 0) ∂volume :=
              lintegral_mono_set (fun s hs => hs.1.le)
          _ = totalIdleTime arrival claims w ω := rfl
      · have hzero : (∫ s in Set.Ioc (0 : ℝ) (t : ℝ), f s ∂volume) = 0 :=
          integral_undef hfInt
        change ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ) (t : ℝ), f s ∂volume) ≤ _
        rw [hzero, ENNReal.ofReal_zero]
        exact bot_le
    exact lt_of_lt_of_le hb_lt (le_trans (ENNReal.ofReal_le_ofReal hM_le_int) hInt_le_idle)
  have hCompl : P ({ω | totalIdleTime arrival claims w ω = ⊤}ᶜ) = 0 := ae_iff.mp hAE_top
  have hProb : P {ω | totalIdleTime arrival claims w ω = ⊤} = 1 := by
    apply le_antisymm
    · exact prob_le_one
    · calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
        _ = P ({ω | totalIdleTime arrival claims w ω = ⊤} ∪
              {ω | totalIdleTime arrival claims w ω = ⊤}ᶜ) := by rw [Set.union_compl_self]
        _ ≤ P {ω | totalIdleTime arrival claims w ω = ⊤} +
              P ({ω | totalIdleTime arrival claims w ω = ⊤}ᶜ) := measure_union_le _ _
        _ = P {ω | totalIdleTime arrival claims w ω = ⊤} := by rw [hCompl, add_zero]
  rw [hProb]
  simp
