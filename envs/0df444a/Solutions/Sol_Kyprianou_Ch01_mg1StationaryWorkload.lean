-- Prove2me | solution 1 for Kyprianou.Ch01.mg1StationaryWorkload
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T18:08:13.134746+00:00
-- url     : https://prove2.me/submissions/87deaf37-6935-49e0-9581-61dd43491d6f

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_ruinDeficitIntegratedTail
import Theorems.Thm_Kyprianou_Ch01_pollaczekKhintchineRuin
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_indep_stationary
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false
universe u

private lemma integrable_id_expMeasure_sw {r : ℝ} (hr : 0 < r) :
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
    · rw [Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
      simp only [gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx),
        gammaPDF_of_neg (lt_of_not_ge hx)]
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

private lemma integral_id_expMeasure_sw {r : ℝ} (hr : 0 < r) :
    (∫ x, x ∂(expMeasure r)) = 1 / r := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hlt : ∀ᵐ x ∂volume, gammaPDF 1 r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have hEq : (fun x : ℝ => (gammaPDF 1 r x).toReal • x) =
      (Set.Ici (0 : ℝ)).indicator (fun x : ℝ => r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)))) := by
    ext x
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
      simp only [smul_eq_mul, gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one,
        div_one, sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      have h21 : (2 : ℝ) - 1 = 1 := by norm_num
      rw [h21, Real.rpow_one]
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx),
        gammaPDF_of_neg (lt_of_not_ge hx)]
      simp
  rw [hEq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hInt : (∫ x in Set.Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)) ∂volume) =
      (1 / r) ^ (2 : ℝ) * Real.Gamma 2 := by
    simpa [neg_mul] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) hr)
  rw [hInt]
  have hG2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    simp
  rw [hG2, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp [hr.ne']

private lemma measurable_riskSurplus_sw
    {Ω : Type u} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (hArr : ∀ n, Measurable (arrival n))
    (hClm : ∀ n, Measurable (claims n))
    (t : ℝ≥0) :
    Measurable (riskSurplus arrival claims 1 0 t) := by
  have hArrSum : ∀ n, Measurable (fun ω => ProbabilityTheory.arrival arrival n ω) := fun n =>
    Finset.measurable_sum (Finset.range (n + 1)) (fun i _ => hArr i)
  have hJC : Measurable (fun ω =>
      jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)) := by
    refine measurable_to_countable' fun k => ?_
    cases k with
    | zero =>
        have hEq : (fun ω => jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)) ⁻¹' {0} =
            {ω | (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω} ∪
            ⋂ n : ℕ, {ω | ProbabilityTheory.arrival arrival n ω ≤ (t : ℝ)} := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
            Set.mem_iInter, jumpCount]
          constructor
          · intro h0
            by_cases hne : ({n : ℕ | (t : ℝ) < ProbabilityTheory.arrival arrival n ω}).Nonempty
            · left; have hmem := Nat.sInf_mem hne; rwa [h0] at hmem
            · right; intro n; by_contra hgt; exact hne ⟨n, lt_of_not_ge hgt⟩
          · rintro (h0 | hall)
            · exact Nat.eq_zero_of_le_zero (Nat.sInf_le h0)
            · have hemp : {n : ℕ | (t : ℝ) < ProbabilityTheory.arrival arrival n ω} = ∅ := by
                ext n; simp [not_lt.mpr (hall n)]
              rw [hemp, Nat.sInf_empty]
        rw [hEq]
        exact (measurableSet_lt measurable_const (hArrSum 0)).union
          (MeasurableSet.iInter fun n => measurableSet_le (hArrSum n) measurable_const)
    | succ j =>
        have hEq : (fun ω => jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)) ⁻¹' {j + 1} =
            {ω | (t : ℝ) < ProbabilityTheory.arrival arrival (j + 1) ω} ∩
            ⋂ i ∈ Finset.range (j + 1), {ω | ProbabilityTheory.arrival arrival i ω ≤ (t : ℝ)} := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_iInter, Finset.mem_range, jumpCount]
          constructor
          · intro hj
            have hne : ({n : ℕ | (t : ℝ) < ProbabilityTheory.arrival arrival n ω}).Nonempty := by
              by_contra hemp
              rw [Set.not_nonempty_iff_eq_empty] at hemp
              rw [hemp, Nat.sInf_empty] at hj
              exact Nat.succ_ne_zero j hj.symm
            constructor
            · have hmem := Nat.sInf_mem hne; rwa [hj] at hmem
            · intro i hi
              by_contra hgt
              have hlt' : (t : ℝ) < ProbabilityTheory.arrival arrival i ω := lt_of_not_ge hgt
              have hle := Nat.sInf_le (s := {n : ℕ | (t : ℝ) < ProbabilityTheory.arrival arrival n ω}) hlt'
              omega
          · rintro ⟨hgt, hle⟩
            apply le_antisymm
            · exact Nat.sInf_le hgt
            · refine le_csInf ⟨j + 1, hgt⟩ ?_
              intro n hn
              by_contra hlt
              exact not_lt_of_ge (hle n (lt_of_not_ge hlt)) hn
        rw [hEq]
        exact (measurableSet_lt measurable_const (hArrSum (j + 1))).inter
          (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ =>
            measurableSet_le (hArrSum i) measurable_const)
  have hSumClm : Measurable (fun ω =>
      ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
        claims i ω) := by
    intro s hs
    have hEq : (fun ω =>
        ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
          claims i ω) ⁻¹' s =
        ⋃ k : ℕ, ((fun ω => jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)) ⁻¹' {k}) ∩
          ((fun ω => ∑ i ∈ Finset.range k, claims i ω) ⁻¹' s) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨k, hk, h⟩; rwa [hk]
    rw [hEq]
    exact MeasurableSet.iUnion fun k =>
      (hJC (measurableSet_singleton k)).inter
        ((Finset.measurable_sum (Finset.range k) fun i _ => hClm i) hs)
  have hEq : riskSurplus arrival claims 1 0 t =
      fun ω => 0 + 1 * (t : ℝ) - (0 + 0 * (t : ℝ) +
        ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
          claims i ω) := by
    ext ω
    simp [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
      ProbabilityTheory.piecewisePath]
  rw [hEq]
  exact measurable_const.sub (measurable_const.add hSumClm)

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
    (hlight : (rate : ℝ) * mu < 1)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    ∀ w : ℝ, 0 ≤ w → ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal)
        atTop (nhds (pkCDF eta ((rate : ℝ) * mu) x)) := by
  intro w hw x hx
  set X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
  have hX_meas : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
    measurable_riskSurplus_sw arrival claims hd.measurable_interarrival hd.measurable_mark t
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  have hArrPos := hd.ae_interarrival_pos hrate
  have hStrict := hd.ae_strictMono_arrival hrate
  have hTendsto := hd.ae_tendsto_arrival hrate
  have hClaimsPos : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    have hzero : P {ω | claims n ω ≤ 0} = 0 := by
      have hpre : {ω | claims n ω ≤ 0} = claims n ⁻¹' Set.Iic (0 : ℝ) := rfl
      rw [hpre, ← Measure.map_apply (hd.measurable_mark n) measurableSet_Iic,
        (hd.law_mark n).map_eq, hclaimpos]
    rw [ae_iff]
    convert hzero using 2
    ext ω; simp [not_lt]
  -- Step 1: Identify pkCDF eta (rate * mu) x = 1 - ruinProbability P arrival claims 1 x
  have hRuinDef := Kyprianou.Ch01.ruinDeficitIntegratedTail P arrival claims rate F hd hrate mu hmu
    hclaimpos hclaimint hmean 1 zero_lt_one hlight
  have hRuin0 : ruinProbability P arrival claims 1 0 = (rate : ℝ) * mu := by
    simpa using hRuinDef.1
  have hPK : 1 - ruinProbability P arrival claims 1 x = pkCDF eta ((rate : ℝ) * mu) x := by
    have h := Kyprianou.Ch01.pollaczekKhintchineRuin P arrival claims rate F hd hrate mu hmu
      hclaimpos hclaimint hmean 1 zero_lt_one hlight eta hetaSupport
      (fun y hy => by rw [heta y hy]; exact hRuinDef.2 y hy) x hx
    rwa [hRuin0] at h
  -- Step 2: SLLN → X t → +∞ a.s. (so coupling W_t^(w) = W_t^(0) holds eventually a.s.)
  have hX_tendsto_top : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => X t ω) atTop atTop := by
    have hArr_iid : Pairwise (fun i j => IndepFun (arrival i) (arrival j) P) := fun i j hij =>
      hd.indep.indepFun (show (Sum.inl i : ℕ ⊕ ℕ) ≠ Sum.inl j by simp [hij])
    have hArr_ident : ∀ i, IdentDistrib (arrival i) (arrival 0) P P := fun i =>
      { aemeasurable_fst := (hd.measurable_interarrival i).aemeasurable
        aemeasurable_snd := (hd.measurable_interarrival 0).aemeasurable
        map_eq := by rw [(hd.law_interarrival i).map_eq, (hd.law_interarrival 0).map_eq] }
    have hArr_int : Integrable (arrival 0) P := by
      have h1 := integrable_id_expMeasure_sw hrateR
      rw [← (hd.law_interarrival 0).map_eq] at h1
      exact (integrable_map_measure h1.aestronglyMeasurable
        (hd.measurable_interarrival 0).aemeasurable).mp h1
    have hArr_mean : (∫ ω, arrival 0 ω ∂P) = 1 / (rate : ℝ) := by
      have hmap := integral_map (μ := P) (φ := arrival 0) (f := fun x : ℝ => x)
        (hd.measurable_interarrival 0).aemeasurable (by fun_prop)
      rw [← hmap, (hd.law_interarrival 0).map_eq]
      exact integral_id_expMeasure_sw hrateR
    have hSLLN_arr := ProbabilityTheory.strong_law_ae_real arrival hArr_int hArr_iid hArr_ident
    rw [hArr_mean] at hSLLN_arr
    have hClm_iid : Pairwise (fun i j => IndepFun (claims i) (claims j) P) := fun i j hij =>
      hd.indep.indepFun (show (Sum.inr i : ℕ ⊕ ℕ) ≠ Sum.inr j by simp [hij])
    have hClm_ident : ∀ i, IdentDistrib (claims i) (claims 0) P P := fun i =>
      { aemeasurable_fst := (hd.measurable_mark i).aemeasurable
        aemeasurable_snd := (hd.measurable_mark 0).aemeasurable
        map_eq := by rw [(hd.law_mark i).map_eq, (hd.law_mark 0).map_eq] }
    have hClm_int : Integrable (claims 0) P := by
      have h1 := hclaimint
      rw [← (hd.law_mark 0).map_eq] at h1
      exact (integrable_map_measure h1.aestronglyMeasurable
        (hd.measurable_mark 0).aemeasurable).mp h1
    have hClm_mean : (∫ ω, claims 0 ω ∂P) = mu := by
      have hmap := integral_map (μ := P) (φ := claims 0) (f := fun x : ℝ => x)
        (hd.measurable_mark 0).aemeasurable (by fun_prop)
      rw [← hmap, (hd.law_mark 0).map_eq]
      exact hmean
    have hSLLN_clm := ProbabilityTheory.strong_law_ae_real claims hClm_int hClm_iid hClm_ident
    rw [hClm_mean] at hSLLN_clm
    filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos, hSLLN_arr, hSLLN_clm] with
      ω hPosω hStrictω hTendstoω hClmω hArrω hClmSLLN
    rw [tendsto_atTop]
    intro B
    rw [Filter.eventually_atTop]
    have hArr_lim : Tendsto (fun n : ℕ => ProbabilityTheory.arrival arrival n ω / ((n : ℝ) + 1))
        atTop (𝓝 (1 / (rate : ℝ))) := by
      have hEq : (fun n : ℕ => ProbabilityTheory.arrival arrival n ω / ((n : ℝ) + 1)) =
          fun n => (∑ i ∈ Finset.range (n + 1), arrival i ω) / ((n + 1 : ℕ) : ℝ) := by
        ext n; simp [ProbabilityTheory.arrival]
      rw [hEq]
      exact hArrω.comp (tendsto_add_atTop_nat 1)
    set α : ℝ := (1 + (rate : ℝ) * mu) / 2
    have hα_lt1 : α < 1 := by dsimp [α]; linarith
    have hrm_lt_α : (rate : ℝ) * mu < α := by dsimp [α]; linarith
    have hRatio : Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.range (n + 1), claims i ω) / ProbabilityTheory.arrival arrival n ω)
        atTop (𝓝 ((rate : ℝ) * mu)) := by
      have hEq : (fun n : ℕ =>
          (∑ i ∈ Finset.range (n + 1), claims i ω) / ProbabilityTheory.arrival arrival n ω) =
          fun n => ((∑ i ∈ Finset.range (n + 1), claims i ω) / ((n + 1 : ℕ) : ℝ)) /
            (ProbabilityTheory.arrival arrival n ω / ((n : ℝ) + 1)) := by
        ext n
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast, div_div_div_cancel_right₀ hn]
      rw [hEq]
      have hnum : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), claims i ω) / ((n + 1 : ℕ) : ℝ))
          atTop (𝓝 mu) := hClmSLLN.comp (tendsto_add_atTop_nat 1)
      have hdiv := hnum.div hArr_lim (by positivity : (1 / (rate : ℝ)) ≠ 0)
      have hval : mu / (1 / (rate : ℝ)) = (rate : ℝ) * mu := by field_simp [hrateR.ne']
      rwa [hval] at hdiv
    have hRat_ev := hRatio.eventually (gt_mem_nhds hrm_lt_α)
    rw [Filter.eventually_atTop] at hRat_ev
    obtain ⟨M0, hM0⟩ := hRat_ev
    set S_cap : ℝ := ∑ i ∈ Finset.range (M0 + 1), claims i ω
    set T0R : ℝ := max (max (B + S_cap) (B / (1 - α))) 1
    have hT0_nn : 0 ≤ T0R := le_trans zero_le_one (le_max_right _ _)
    refine ⟨⟨T0R, hT0_nn⟩, fun t ht => ?_⟩
    have htR : T0R ≤ (t : ℝ) := ht
    have hXt : X t ω = (t : ℝ) -
        ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
          claims i ω := by
      simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath]
    rw [hXt]
    rcases hj : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) with _ | k
    · simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
      have hS_nn : 0 ≤ S_cap := Finset.sum_nonneg fun i _ => (hClmω i).le
      have : B + S_cap ≤ (t : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htR
      linarith
    · by_cases hk : k < M0
      · have hle : ∑ i ∈ Finset.range (k + 1), claims i ω ≤ S_cap :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun i _ _ => (hClmω i).le)
        have : B + S_cap ≤ (t : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htR
        linarith
      · have hk_ge : M0 ≤ k := le_of_not_gt hk
        have hTk_pos : 0 < ProbabilityTheory.arrival arrival k ω := by
          have h0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
            simpa [ProbabilityTheory.arrival] using hPosω 0
          exact lt_of_lt_of_le h0 (hStrictω.monotone (Nat.zero_le k))
        have hTk_le : ProbabilityTheory.arrival arrival k ω ≤ (t : ℝ) :=
          (lt_jumpCount_iff hStrictω hTendstoω k (t : ℝ)).mp (by omega)
        have hrat_k : (∑ i ∈ Finset.range (k + 1), claims i ω) /
            ProbabilityTheory.arrival arrival k ω < α := hM0 k hk_ge
        have hsum_le : ∑ i ∈ Finset.range (k + 1), claims i ω ≤ α * (t : ℝ) := by
          have h1 : ∑ i ∈ Finset.range (k + 1), claims i ω < α * ProbabilityTheory.arrival arrival k ω :=
            (div_lt_iff₀ hTk_pos).mp hrat_k
          have hα_pos : 0 < α := by dsimp [α]; positivity
          nlinarith
        have hB_le : B / (1 - α) ≤ (t : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htR
        have h1α_pos : 0 < 1 - α := by linarith
        have hB2 : B ≤ (1 - α) * (t : ℝ) := by linarith [(div_le_iff₀ h1α_pos).mp hB_le]
        linarith
  -- Step 3: Duality for w = 0: for every t : ℝ≥0, P {W_t^(0) ≤ x} = P {∀ u ≤ t, -X u ≤ x}
  have hDuality : ∀ t : ℝ≥0,
      P {ω | queueWorkload arrival claims 0 t ω ≤ x} =
        P {ω | ∀ u : ℝ≥0, u ≤ t → -X u ω ≤ x} := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      have hEq_ae : {ω | queueWorkload arrival claims 0 0 ω ≤ x} =ᵐ[P]
          {ω | ∀ u : ℝ≥0, u ≤ 0 → -X u ω ≤ x} := by
        filter_upwards [hArrPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
        have hX0 : X 0 ω = 0 := by
          have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
            simpa [ProbabilityTheory.arrival] using hPosω 0
          have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
            have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
              rw [lt_jumpCount_iff hStrictω hTendstoω]; exact not_le.mpr hT0
            omega
          simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hj0]
        have hSet0 : {z : ℝ | ∃ s : ℝ≥0, s ≤ 0 ∧ z = X s ω} = {0} := by
          ext z; simp [hX0]
        have hW0 : queueWorkload arrival claims 0 0 ω = 0 := by
          change max 0 (sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ 0 ∧ z = X s ω}) - X 0 ω = 0
          rw [hSet0, csSup_singleton, hX0]; simp
        change (queueWorkload arrival claims 0 0 ω ≤ x) = (∀ u : ℝ≥0, u ≤ 0 → -X u ω ≤ x)
        apply propext
        rw [hW0]
        exact ⟨fun _ u hu => by rw [le_zero_iff.mp hu, hX0, neg_zero]; exact hx, fun _ => hx⟩
      exact measure_congr hEq_ae
    · have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht0
      -- Dyadic grid reversal for m = 2^n steps of size h = t / 2^n
      have hGrid_eq : ∀ n : ℕ,
          let m : ℕ := 2 ^ n
          let h : ℝ≥0 := t / (m : ℝ≥0)
          P {ω | ∀ k ≤ m, X (k • h) ω - X t ω ≤ x} =
            P {ω | ∀ r ≤ m, -X (r • h) ω ≤ x} := by
        intro n m h
        have hm_pos : 0 < m := pow_pos (by norm_num) n
        have hm_ne : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
        have hmh : m • h = t := by
          rw [nsmul_eq_mul]; exact mul_div_cancel₀ t hm_ne
        let Δ : Fin m → Ω → ℝ := fun j ω => X ((j.1 + 1) • h) ω - X (j.1 • h) ω
        have hΔ_meas : ∀ j : Fin m, Measurable (Δ j) := fun j =>
          (hX_meas _).sub (hX_meas _)
        -- Law of (Δ_0, ..., Δ_{m-1}) is Measure.pi (fun _ => P.map (X h))
        have hLaw_pi : P.map (fun ω (j : Fin m) => Δ j ω) =
            Measure.pi (fun _ : Fin m => P.map (X h)) := by
          have : IsProbabilityMeasure (P.map (X h)) := Measure.isProbabilityMeasure_map (hX_meas h).aemeasurable
          symm
          refine Measure.pi_eq fun s hs => ?_
          rw [Measure.map_apply (measurable_pi_lambda _ hΔ_meas) (MeasurableSet.univ_pi hs)]
          have hpre : (fun ω (j : Fin m) => Δ j ω) ⁻¹' Set.univ.pi s =
              ⋂ j : Fin m, Δ j ⁻¹' s j := by
            ext ω; simp [Set.mem_pi]
          rw [hpre]
          -- Induction on prefix length r ≤ m
          have hPref : ∀ (r : ℕ) (hr : r ≤ m),
              P (⋂ j ∈ (Finset.univ.filter fun j : Fin m => j.1 < r), Δ j ⁻¹' s j) =
                ∏ j ∈ (Finset.univ.filter fun j : Fin m => j.1 < r), (P.map (X h)) (s j) := by
            intro r
            induction r with
            | zero =>
                intro _
                have hemp : (Finset.univ.filter fun j : Fin m => j.1 < 0) = ∅ := by
                  ext j; simp
                rw [hemp]; simp
            | succ r ih =>
                intro hr
                let j_last : Fin m := ⟨r, hr⟩
                have hFilter_eq : (Finset.univ.filter fun j : Fin m => j.1 < r + 1) =
                    insert j_last (Finset.univ.filter fun j : Fin m => j.1 < r) := by
                  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                    Fin.ext_iff, j_last]
                  omega
                have hnotmem : j_last ∉ Finset.univ.filter (fun j : Fin m => j.1 < r) := by
                  simp [j_last]
                rw [hFilter_eq, Finset.prod_insert hnotmem]
                have hInter_eq : (⋂ j ∈ insert j_last (Finset.univ.filter fun j : Fin m => j.1 < r),
                    Δ j ⁻¹' s j) =
                    (⋂ j ∈ Finset.univ.filter (fun j : Fin m => j.1 < r), Δ j ⁻¹' s j) ∩
                    (Δ j_last ⁻¹' s j_last) := by
                  ext ω; simp [Set.mem_iInter, and_comm]
                rw [hInter_eq]
                have hst : r • h ≤ (r + 1) • h := by
                  rw [nsmul_eq_mul, nsmul_eq_mul]
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ r) h.2
                have hRS := Kyprianou.Ch01.riskSurplus_increment_indep_stationary
                  P arrival claims rate hrate F hd 1 (r • h) ((r + 1) • h) hst
                have hA_meas : MeasurableSet[naturalSigma X (r • h)]
                    (⋂ j ∈ Finset.univ.filter (fun j : Fin m => j.1 < r), Δ j ⁻¹' s j) := by
                  have hXle : ∀ u : ℕ, u ≤ r →
                      @Measurable Ω ℝ (naturalSigma X (r • h)) _ (X (u • h)) := fun u hu => by
                    have hule : u • h ≤ r • h := by
                      rw [nsmul_eq_mul, nsmul_eq_mul]
                      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu) h.2
                    exact (comap_measurable (X (u • h))).mono (le_iSup₂_of_le (u • h) hule le_rfl) le_rfl
                  refine @MeasurableSet.biInter _ _ (naturalSigma X (r • h)) _ _
                    (Finset.countable_toSet _) fun j hj => ?_
                  have hjlt : j.1 < r := (Finset.mem_filter.mp hj).2
                  exact ((hXle (j.1 + 1) (by omega)).sub (hXle j.1 (by omega))) (hs j)
                have hB_meas : MeasurableSet[MeasurableSpace.comap (Δ j_last) inferInstance]
                    (Δ j_last ⁻¹' s j_last) := ⟨s j_last, hs j_last, rfl⟩
                have hMul := (Indep_iff _ _ P).mp hRS.1.symm _ _ hA_meas hB_meas
                rw [hMul, ih (Nat.le_of_succ_le hr), mul_comm]
                congr 1
                have hsub : (r + 1) • h - r • h = h := by
                  rw [succ_nsmul, add_tsub_cancel_left]
                rw [← Measure.map_apply (hΔ_meas j_last) (hs j_last)]
                have hStat := hRS.2
                rw [hsub] at hStat
                exact congrArg (fun μ => μ (s j_last)) hStat
          have hAll := hPref m le_rfl
          have hUniv : (Finset.univ.filter fun j : Fin m => j.1 < m) = Finset.univ := by
            ext j; simp [j.2]
          rw [hUniv] at hAll
          simpa using hAll
        -- Reversal preserves Measure.pi (fun _ => P.map (X h))
        let rev : (Fin m → ℝ) → (Fin m → ℝ) := fun v j => v j.rev
        have hrev_meas : Measurable rev := measurable_pi_lambda _ fun j => measurable_pi_apply j.rev
        have hRev_law : (P.map (fun ω (j : Fin m) => Δ j ω)).map rev =
            P.map (fun ω (j : Fin m) => Δ j ω) := by
          rw [hLaw_pi]
          have : IsProbabilityMeasure (P.map (X h)) := Measure.isProbabilityMeasure_map (hX_meas h).aemeasurable
          symm
          refine Measure.pi_eq fun s hs => ?_
          rw [Measure.map_apply hrev_meas (MeasurableSet.univ_pi hs)]
          have hpre : rev ⁻¹' Set.univ.pi s = Set.univ.pi (fun j : Fin m => s j.rev) := by
            ext v
            simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, rev]
            constructor
            · intro hv j; simpa [Fin.rev_rev] using hv j.rev
            · intro hv j; simpa [Fin.rev_rev] using hv j.rev
          rw [hpre, Measure.pi_pi]
          symm
          exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => by simp [Fin.revPerm])
        -- Apply functional G : (Fin m → ℝ) → Prop, ∀ r ≤ m, -(∑_{j < r} v j) ≤ x
        let GoodSet : Set (Fin m → ℝ) :=
          ⋂ r ∈ Finset.range (m + 1), {v : Fin m → ℝ | -(∑ j : Fin m, if j.1 < r then v j else 0) ≤ x}
        have hGood_meas : MeasurableSet GoodSet := by
          refine MeasurableSet.biInter (Finset.countable_toSet _) fun r _ => ?_
          refine measurableSet_le ?_ measurable_const
          refine (Finset.measurable_sum Finset.univ fun j _ => ?_).neg
          by_cases hj : j.1 < r
          · simp only [if_pos hj]; exact measurable_pi_apply j
          · simp only [if_neg hj]; exact measurable_const
        have hMap_eq := congrArg (fun μ => μ GoodSet) hRev_law
        rw [Measure.map_map hrev_meas (measurable_pi_lambda _ hΔ_meas),
          Measure.map_apply (hrev_meas.comp (measurable_pi_lambda _ hΔ_meas)) hGood_meas,
          Measure.map_apply (measurable_pi_lambda _ hΔ_meas) hGood_meas] at hMap_eq
        -- Show the two preimages agree a.e. (using X 0 = 0 a.s.)
        have hX0_ae : ∀ᵐ ω ∂P, X 0 ω = 0 := by
          filter_upwards [hArrPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
          have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
            simpa [ProbabilityTheory.arrival] using hPosω 0
          have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
            have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
              rw [lt_jumpCount_iff hStrictω hTendstoω]; exact not_le.mpr hT0
            omega
          simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hj0]
        have hPre1 : {ω | ∀ k ≤ m, X (k • h) ω - X t ω ≤ x} =ᵐ[P]
            (rev ∘ fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet := by
          filter_upwards [hX0_ae] with ω _
          have hmem : ω ∈ (rev ∘ fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet ↔
              ∀ r ≤ m, -(∑ j : Fin m, if j.1 < r then Δ j.rev ω else 0) ≤ x := by
            simp [GoodSet, rev]
          change (∀ k ≤ m, X (k • h) ω - X t ω ≤ x) =
            (ω ∈ (rev ∘ fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet)
          rw [propext hmem]
          apply propext
          have hTel_rev : ∀ r ≤ m,
              (∑ j : Fin m, if j.1 < r then Δ j.rev ω else 0) =
                X (m • h) ω - X ((m - r) • h) ω := by
            intro r hr
            induction r with
            | zero => simp
            | succ r ih =>
                have hstep : (∑ j : Fin m, if j.1 < r + 1 then Δ j.rev ω else 0) =
                    (∑ j : Fin m, if j.1 < r then Δ j.rev ω else 0) + Δ (⟨r, hr⟩ : Fin m).rev ω := by
                  have hsplit : ∀ j : Fin m,
                      (if j.1 < r + 1 then Δ j.rev ω else 0) =
                      (if j.1 < r then Δ j.rev ω else 0) + (if j = ⟨r, hr⟩ then Δ j.rev ω else 0) := by
                    intro j
                    by_cases h1 : j.1 < r
                    · have hne : j ≠ ⟨r, hr⟩ := fun heq => by rw [heq] at h1; exact lt_irrefl _ h1
                      simp [h1, Nat.lt_succ_of_lt h1, hne]
                    · by_cases h2 : j = ⟨r, hr⟩
                      · subst h2; simp
                      · have hnot : ¬ j.1 < r + 1 := by
                          intro hlt; apply h2; ext; dsimp; omega
                        simp [h1, h2, hnot]
                  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                rw [hstep, ih (Nat.le_of_succ_le hr)]
                dsimp only [Δ, Fin.rev]
                have h1 : m - (r + 1) + 1 = m - r := by omega
                rw [h1]; ring
          constructor
          · intro hall r hr
            rw [hTel_rev r hr, hmh]
            have hle := hall (m - r) (Nat.sub_le m r)
            linarith
          · intro hall k hk
            have hle := hall (m - k) (Nat.sub_le m k)
            rw [hTel_rev (m - k) (Nat.sub_le m k), hmh, Nat.sub_sub_self hk] at hle
            linarith
        have hPre2 : {ω | ∀ r ≤ m, -X (r • h) ω ≤ x} =ᵐ[P]
            (fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet := by
          filter_upwards [hX0_ae] with ω hX0ω
          have hmem : ω ∈ (fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet ↔
              ∀ r ≤ m, -(∑ j : Fin m, if j.1 < r then Δ j ω else 0) ≤ x := by
            simp [GoodSet]
          change (∀ r ≤ m, -X (r • h) ω ≤ x) =
            (ω ∈ (fun ω (j : Fin m) => Δ j ω) ⁻¹' GoodSet)
          rw [propext hmem]
          apply propext
          have hTel : ∀ r ≤ m,
              (∑ j : Fin m, if j.1 < r then Δ j ω else 0) = X (r • h) ω := by
            intro r hr
            induction r with
            | zero => simp [hX0ω]
            | succ r ih =>
                have hstep : (∑ j : Fin m, if j.1 < r + 1 then Δ j ω else 0) =
                    (∑ j : Fin m, if j.1 < r then Δ j ω else 0) + Δ ⟨r, hr⟩ ω := by
                  have hsplit : ∀ j : Fin m,
                      (if j.1 < r + 1 then Δ j ω else 0) =
                      (if j.1 < r then Δ j ω else 0) + (if j = ⟨r, hr⟩ then Δ j ω else 0) := by
                    intro j
                    by_cases h1 : j.1 < r
                    · have hne : j ≠ ⟨r, hr⟩ := fun heq => by rw [heq] at h1; exact lt_irrefl _ h1
                      simp [h1, Nat.lt_succ_of_lt h1, hne]
                    · by_cases h2 : j = ⟨r, hr⟩
                      · subst h2; simp
                      · have hnot : ¬ j.1 < r + 1 := by
                          intro hlt; apply h2; ext; dsimp; omega
                        simp [h1, h2, hnot]
                  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                rw [hstep, ih (Nat.le_of_succ_le hr)]
                dsimp only [Δ]; ring
          constructor <;> intro hall r hr
          · rw [hTel r hr]; exact hall r hr
          · have := hall r hr; rwa [hTel r hr] at this
        rw [measure_congr hPre1, measure_congr hPre2, hMap_eq]
      -- Dyadic limit n → ∞ on decreasing events
      let Lset : ℕ → Set Ω := fun n => {ω | ∀ k ≤ 2 ^ n, X (k • (t / ((2 ^ n : ℕ) : ℝ≥0))) ω - X t ω ≤ x}
      let Rset : ℕ → Set Ω := fun n => {ω | ∀ r ≤ 2 ^ n, -X (r • (t / ((2 ^ n : ℕ) : ℝ≥0))) ω ≤ x}
      have hL_anti : Antitone Lset := fun n1 n2 hn ω hω k hk => by
        have hstep : k • (t / ((2 ^ n1 : ℕ) : ℝ≥0)) = (k * 2 ^ (n2 - n1)) • (t / ((2 ^ n2 : ℕ) : ℝ≥0)) := by
          ext
          simp only [nsmul_eq_mul]
          push_cast
          have hpow : (2 : ℝ) ^ n2 = (2 : ℝ) ^ n1 * (2 : ℝ) ^ (n2 - n1) := by
            rw [← pow_add, Nat.add_sub_of_le hn]
          rw [hpow]
          have h2a : (2 : ℝ) ^ n1 ≠ 0 := pow_ne_zero _ two_ne_zero
          have h2b : (2 : ℝ) ^ (n2 - n1) ≠ 0 := pow_ne_zero _ two_ne_zero
          field_simp [h2a, h2b]
        rw [hstep]
        have hle : k * 2 ^ (n2 - n1) ≤ 2 ^ n2 := by
          calc k * 2 ^ (n2 - n1) ≤ 2 ^ n1 * 2 ^ (n2 - n1) := Nat.mul_le_mul_right _ hk
            _ = 2 ^ n2 := by rw [← pow_add, Nat.add_sub_of_le hn]
        exact hω _ hle
      have hR_anti : Antitone Rset := fun n1 n2 hn ω hω r hr => by
        have hstep : r • (t / ((2 ^ n1 : ℕ) : ℝ≥0)) = (r * 2 ^ (n2 - n1)) • (t / ((2 ^ n2 : ℕ) : ℝ≥0)) := by
          ext
          simp only [nsmul_eq_mul]
          push_cast
          have hpow : (2 : ℝ) ^ n2 = (2 : ℝ) ^ n1 * (2 : ℝ) ^ (n2 - n1) := by
            rw [← pow_add, Nat.add_sub_of_le hn]
          rw [hpow]
          have h2a : (2 : ℝ) ^ n1 ≠ 0 := pow_ne_zero _ two_ne_zero
          have h2b : (2 : ℝ) ^ (n2 - n1) ≠ 0 := pow_ne_zero _ two_ne_zero
          field_simp [h2a, h2b]
        rw [hstep]
        have hle : r * 2 ^ (n2 - n1) ≤ 2 ^ n2 := by
          calc r * 2 ^ (n2 - n1) ≤ 2 ^ n1 * 2 ^ (n2 - n1) := Nat.mul_le_mul_right _ hr
            _ = 2 ^ n2 := by rw [← pow_add, Nat.add_sub_of_le hn]
        exact hω _ hle
      have hL_meas : ∀ n, MeasurableSet (Lset n) := fun n => by
        have hEq : Lset n = ⋂ k ∈ Finset.range (2 ^ n + 1),
            {ω | X (k • (t / ((2 ^ n : ℕ) : ℝ≥0))) ω - X t ω ≤ x} := by ext ω; simp [Lset]
        rw [hEq]
        exact MeasurableSet.biInter (Finset.countable_toSet _) fun k _ =>
          measurableSet_le ((hX_meas _).sub (hX_meas t)) measurable_const
      have hR_meas : ∀ n, MeasurableSet (Rset n) := fun n => by
        have hEq : Rset n = ⋂ r ∈ Finset.range (2 ^ n + 1),
            {ω | -X (r • (t / ((2 ^ n : ℕ) : ℝ≥0))) ω ≤ x} := by ext ω; simp [Rset]
        rw [hEq]
        exact MeasurableSet.biInter (Finset.countable_toSet _) fun r _ =>
          measurableSet_le (hX_meas _).neg measurable_const
      -- Right-continuity of X on [0, t] gives ⋂ Lset = {W_t^(0) ≤ x} and ⋂ Rset = {∀ u ≤ t, -X u ≤ x} a.e.
      have hLim_ae : ∀ᵐ ω ∂P,
          (queueWorkload arrival claims 0 t ω ≤ x ↔ ω ∈ ⋂ n : ℕ, Lset n) ∧
          ((∀ u : ℝ≥0, u ≤ t → -X u ω ≤ x) ↔ ω ∈ ⋂ n : ℕ, Rset n) := by
        filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos] with ω hPosω hStrictω hTendstoω hClmω
        have hX0 : X 0 ω = 0 := by
          have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
            simpa [ProbabilityTheory.arrival] using hPosω 0
          have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
            have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
              rw [lt_jumpCount_iff hStrictω hTendstoω]; exact not_le.mpr hT0
            omega
          simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hj0]
        have hBdd : BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} := by
          refine ⟨(t : ℝ), ?_⟩
          rintro z ⟨s, hs, rfl⟩
          have hAgg : 0 ≤ aggregateClaims arrival claims s ω := by
            simp only [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]
            have : 0 ≤ ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)),
                claims i ω := Finset.sum_nonneg fun i _ => (hClmω i).le
            linarith
          have hsR : (s : ℝ) ≤ (t : ℝ) := hs
          simp only [X, riskSurplus]; linarith
        have hSup_nonneg : 0 ≤ sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} := by
          rw [← hX0]; exact le_csSup hBdd ⟨0, zero_le, rfl⟩
        -- Right-continuity: for any u < t, there is δ > 0 with X v = X u + (v - u) on [u, u + δ)
        have hRightConst : ∀ u : ℝ≥0, u < t → ∃ δ : ℝ, 0 < δ ∧
            ∀ v : ℝ≥0, (u : ℝ) ≤ (v : ℝ) → (v : ℝ) < (u : ℝ) + δ →
              X v ω = X u ω + ((v : ℝ) - (u : ℝ)) := by
          intro u _
          set j := jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (u : ℝ)
          have hTj_gt : (u : ℝ) < ProbabilityTheory.arrival arrival j ω := by
            by_contra hle
            have hlt := (lt_jumpCount_iff hStrictω hTendstoω j (u : ℝ)).mpr (le_of_not_gt hle)
            exact lt_irrefl _ hlt
          refine ⟨ProbabilityTheory.arrival arrival j ω - (u : ℝ), by linarith, fun v huv hvlt => ?_⟩
          have hJC_v : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (v : ℝ) = j := by
            apply le_antisymm
            · by_contra hgt
              have hlt : j < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (v : ℝ) :=
                lt_of_not_ge hgt
              have hle := (lt_jumpCount_iff hStrictω hTendstoω j (v : ℝ)).mp hlt
              linarith
            · by_contra hlt
              have hlt' : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (v : ℝ) < j :=
                lt_of_not_ge hlt
              set m := jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (v : ℝ)
              have hTm_le : ProbabilityTheory.arrival arrival m ω ≤ (u : ℝ) :=
                (lt_jumpCount_iff hStrictω hTendstoω m (u : ℝ)).mp hlt'
              have hTm_lt_v : m < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (v : ℝ) :=
                (lt_jumpCount_iff hStrictω hTendstoω m (v : ℝ)).mpr (le_trans hTm_le huv)
              exact lt_irrefl _ hTm_lt_v
          simp only [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hJC_v]
          ring
        -- Helper: for any u < t and ε > 0, there exists dyadic point k • (t / 2^n) in [u, min t (u + ε))
        have hDyadic_in : ∀ (u : ℝ≥0), u < t → ∀ ε : ℝ, 0 < ε →
            ∃ n k : ℕ, k ≤ 2 ^ n ∧
              (u : ℝ) ≤ ((k • (t / ((2 ^ n : ℕ) : ℝ≥0)) : ℝ≥0) : ℝ) ∧
              ((k • (t / ((2 ^ n : ℕ) : ℝ≥0)) : ℝ≥0) : ℝ) < (u : ℝ) + ε := by
          intro u hut ε hε
          set η : ℝ := min ε ((t : ℝ) - (u : ℝ))
          have hη_pos : 0 < η := lt_min hε (sub_pos.mpr (NNReal.coe_lt_coe.mpr hut))
          have htR_pos : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht_pos
          obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / η)
          have h2n : (t : ℝ) / η < (2 : ℝ) ^ n := by
            have : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast Nat.lt_two_pow_self
            linarith
          set step : ℝ := (t : ℝ) / (2 : ℝ) ^ n
          have hstep_pos : 0 < step := div_pos htR_pos (pow_pos (two_pos : (0 : ℝ) < 2) n)
          have hstep_lt : step < η := by
            dsimp only [step]
            rw [div_lt_iff₀ (pow_pos (two_pos : (0 : ℝ) < 2) n)]
            rw [div_lt_iff₀ hη_pos] at h2n
            linarith
          set k : ℕ := Nat.ceil ((u : ℝ) / step)
          have hk_ge : (u : ℝ) ≤ (k : ℝ) * step := by
            have := Nat.le_ceil ((u : ℝ) / step)
            rwa [div_le_iff₀ hstep_pos] at this
          have hk_lt : (k : ℝ) * step < (u : ℝ) + step := by
            have h1 : (k : ℝ) < (u : ℝ) / step + 1 := Nat.ceil_lt_add_one (by positivity)
            have h2 := mul_lt_mul_of_pos_right h1 hstep_pos
            have h3 : ((u : ℝ) / step + 1) * step = (u : ℝ) + step := by field_simp [hstep_pos.ne']
            linarith
          have hk_le_2n : k ≤ 2 ^ n := by
            have hlt_t : (k : ℝ) * step < (t : ℝ) := by
              have : η ≤ (t : ℝ) - (u : ℝ) := min_le_right _ _
              linarith
            have h1 : (k : ℝ) < (2 : ℝ) ^ n := by
              dsimp only [step] at hlt_t
              have h2 : (k : ℝ) * (t : ℝ) < (t : ℝ) * (2 : ℝ) ^ n := by
                have hlt' : (k : ℝ) * (t : ℝ) / (2 : ℝ) ^ n < (t : ℝ) := by
                  rwa [mul_div_assoc]
                exact (div_lt_iff₀ (pow_pos (two_pos : (0 : ℝ) < 2) n)).mp hlt'
              nlinarith
            exact_mod_cast h1.le
          have hcoe : ((k • (t / ((2 ^ n : ℕ) : ℝ≥0)) : ℝ≥0) : ℝ) = (k : ℝ) * step := by
            simp [step, nsmul_eq_mul]
          refine ⟨n, k, hk_le_2n, by rwa [hcoe], ?_⟩
          rw [hcoe]
          have : η ≤ ε := min_le_left _ _
          linarith
        constructor
        · -- Part 1: W_t^(0) ≤ x ↔ ω ∈ ⋂ Lset
          have hW0_eq : queueWorkload arrival claims 0 t ω =
              sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} - X t ω := by
            dsimp only [queueWorkload]; rw [max_eq_right hSup_nonneg]
          rw [hW0_eq]
          constructor
          · intro hle
            rw [Set.mem_iInter]
            intro n k hk
            set s : ℝ≥0 := k • (t / ((2 ^ n : ℕ) : ℝ≥0))
            have hs_le : s ≤ t := by
              rw [← NNReal.coe_le_coe]
              simp only [s, nsmul_eq_mul]
              push_cast
              have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (two_pos : (0 : ℝ) < 2) n
              have hkR : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
              calc (k : ℝ) * ((t : ℝ) / (2 : ℝ) ^ n)
                  ≤ (2 : ℝ) ^ n * ((t : ℝ) / (2 : ℝ) ^ n) :=
                    mul_le_mul_of_nonneg_right hkR (by positivity)
                _ = (t : ℝ) := by field_simp [h2n_pos.ne']
            have hXs_le : X s ω ≤ sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω} :=
              le_csSup hBdd ⟨s, hs_le, rfl⟩
            linarith
          · intro hmem
            rw [Set.mem_iInter] at hmem
            have hSup_le : sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} ≤ X t ω + x := by
              refine csSup_le ⟨X 0 ω, 0, zero_le, rfl⟩ ?_
              rintro z ⟨s, hs, rfl⟩
              rcases eq_or_lt_of_le hs with rfl | hlt
              · linarith
              · by_contra hgt
                have hgt' : X t ω + x < X s ω := lt_of_not_ge hgt
                obtain ⟨δ, hδ_pos, hRC⟩ := hRightConst s hlt
                obtain ⟨n, k, hk, hge, hlt_d⟩ := hDyadic_in s hlt δ hδ_pos
                set v : ℝ≥0 := k • (t / ((2 ^ n : ℕ) : ℝ≥0))
                have hXv := hRC v hge hlt_d
                have hGrid := hmem n k hk
                linarith
            linarith
        · -- Part 2: (∀ u ≤ t, -X u ≤ x) ↔ ω ∈ ⋂ Rset
          constructor
          · intro hall
            rw [Set.mem_iInter]
            intro n r hr
            set u : ℝ≥0 := r • (t / ((2 ^ n : ℕ) : ℝ≥0))
            have hu_le : u ≤ t := by
              rw [← NNReal.coe_le_coe]
              simp only [u, nsmul_eq_mul]
              push_cast
              have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (two_pos : (0 : ℝ) < 2) n
              have hrR : (r : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hr
              calc (r : ℝ) * ((t : ℝ) / (2 : ℝ) ^ n)
                  ≤ (2 : ℝ) ^ n * ((t : ℝ) / (2 : ℝ) ^ n) :=
                    mul_le_mul_of_nonneg_right hrR (by positivity)
                _ = (t : ℝ) := by field_simp [h2n_pos.ne']
            exact hall u hu_le
          · intro hmem u hu
            rw [Set.mem_iInter] at hmem
            rcases eq_or_lt_of_le hu with rfl | hlt
            · have h0 := hmem 0 1 (by norm_num)
              simpa using h0
            · by_contra hgt
              have hgt' : x < -X u ω := lt_of_not_ge hgt
              obtain ⟨δ, hδ_pos, hRC⟩ := hRightConst u hlt
              set ε : ℝ := min δ (-X u ω - x)
              have hε_pos : 0 < ε := lt_min hδ_pos (by linarith)
              obtain ⟨n, r, hr, hge, hlt_d⟩ := hDyadic_in u hlt ε hε_pos
              set v : ℝ≥0 := r • (t / ((2 ^ n : ℕ) : ℝ≥0))
              have hXv := hRC v hge (lt_of_lt_of_le hlt_d (by linarith [min_le_left δ (-X u ω - x)]))
              have hGrid := hmem n r hr
              have : (v : ℝ) - (u : ℝ) < -X u ω - x := by linarith [min_le_right δ (-X u ω - x)]
              linarith
      have hL_lim := tendsto_measure_iInter_atTop (μ := P)
        (fun n => (hL_meas n).nullMeasurableSet) hL_anti ⟨0, measure_ne_top P _⟩
      have hR_lim := tendsto_measure_iInter_atTop (μ := P)
        (fun n => (hR_meas n).nullMeasurableSet) hR_anti ⟨0, measure_ne_top P _⟩
      have hSeq_eq : (⇑P ∘ Lset) = (⇑P ∘ Rset) := funext hGrid_eq
      rw [hSeq_eq] at hL_lim
      have hInter_eq : P (⋂ n : ℕ, Lset n) = P (⋂ n : ℕ, Rset n) :=
        tendsto_nhds_unique hL_lim hR_lim
      have hEq1 : {ω | queueWorkload arrival claims 0 t ω ≤ x} =ᵐ[P] ⋂ n : ℕ, Lset n :=
        hLim_ae.mono fun ω hω => propext hω.1
      have hEq2 : {ω | ∀ u : ℝ≥0, u ≤ t → -X u ω ≤ x} =ᵐ[P] ⋂ n : ℕ, Rset n :=
        hLim_ae.mono fun ω hω => propext hω.2
      rw [measure_congr hEq1, measure_congr hEq2, hInter_eq]
  -- Step 4: As t → ∞, P {∀ u ≤ t, -X u ≤ x} → 1 - ruinProbability P arrival claims 1 x
  have hLim_zero : Tendsto (fun t : ℝ≥0 =>
      (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal)
      atTop (𝓝 (1 - ruinProbability P arrival claims 1 x)) := by
    simp_rw [hDuality]
    let E : ℝ≥0 → Set Ω := fun t => {ω | ∀ u : ℝ≥0, u ≤ t → -X u ω ≤ x}
    have hE_anti : Antitone E := fun t1 t2 h12 ω hω u hu => hω u (le_trans hu h12)
    -- Use integer sequence En := E (n : ℝ≥0) and sandwich arbitrary t between ⌊t⌋ and ⌈t⌉
    have hE_meas_nat : ∀ n : ℕ, NullMeasurableSet (E (n : ℝ≥0)) P := fun n => by
      let S_rat : Set Ω :=
        {ω | -X (n : ℝ≥0) ω ≤ x} ∩
          ⋂ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)},
            {ω | -X ⟨(q.1 : ℝ), by exact_mod_cast q.2.1⟩ ω ≤ x}
      have hRat_eq : E (n : ℝ≥0) =ᵐ[P] S_rat := by
        filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos] with ω hPosω hStrictω hTendstoω _
        change (ω ∈ E (n : ℝ≥0)) = (ω ∈ S_rat)
        dsimp only [S_rat]
        apply propext
        constructor
        · intro h
          refine ⟨h (n : ℝ≥0) le_rfl, Set.mem_iInter.mpr fun q => ?_⟩
          exact h ⟨(q.1 : ℝ), by exact_mod_cast q.2.1⟩ (show (q.1 : ℝ) ≤ ((n : ℝ≥0) : ℝ) by simpa using q.2.2)
        · rintro ⟨hn_le, hrat⟩ u hu
          rw [Set.mem_iInter] at hrat
          rcases eq_or_lt_of_le hu with rfl | hlt
          · exact hn_le
          · by_contra hgt
            have hgt' : x < -X u ω := lt_of_not_ge hgt
            set j := jumpCount (fun m => ProbabilityTheory.arrival arrival m ω) (u : ℝ)
            have hTj_gt : (u : ℝ) < ProbabilityTheory.arrival arrival j ω := by
              by_contra hle
              exact lt_irrefl _ ((lt_jumpCount_iff hStrictω hTendstoω j (u : ℝ)).mpr (le_of_not_gt hle))
            set hi : ℝ := min (min (ProbabilityTheory.arrival arrival j ω) (n : ℝ)) ((u : ℝ) + (-X u ω - x))
            have hu_lt_hi : (u : ℝ) < hi := by
              refine lt_min (lt_min hTj_gt (NNReal.coe_lt_coe.mpr hlt)) (by linarith)
            obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu_lt_hi
            have hq_nn : (0 : ℚ) ≤ q := by exact_mod_cast le_trans u.2 hq1.le
            have hq_le_n : (q : ℝ) ≤ (n : ℝ) :=
              le_trans hq2.le (le_trans (min_le_left _ _) (min_le_right _ _))
            have hq_lt_Tj : (q : ℝ) < ProbabilityTheory.arrival arrival j ω :=
              lt_of_lt_of_le hq2 (le_trans (min_le_left _ _) (min_le_left _ _))
            have hJC_q : jumpCount (fun m => ProbabilityTheory.arrival arrival m ω) (q : ℝ) = j := by
              apply le_antisymm
              · by_contra hgt_j
                have hle := (lt_jumpCount_iff hStrictω hTendstoω j (q : ℝ)).mp (lt_of_not_ge hgt_j)
                linarith
              · by_contra hlt_j
                set m := jumpCount (fun m => ProbabilityTheory.arrival arrival m ω) (q : ℝ)
                have hTm_le : ProbabilityTheory.arrival arrival m ω ≤ (u : ℝ) :=
                  (lt_jumpCount_iff hStrictω hTendstoω m (u : ℝ)).mp (lt_of_not_ge hlt_j)
                exact lt_irrefl _ ((lt_jumpCount_iff hStrictω hTendstoω m (q : ℝ)).mpr (le_trans hTm_le hq1.le))
            have hXq : X ⟨(q : ℝ), by exact_mod_cast hq_nn⟩ ω = X u ω + ((q : ℝ) - (u : ℝ)) := by
              dsimp only [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
                ProbabilityTheory.piecewisePath]
              change 0 + 1 * (q : ℝ) -
                  (0 + 0 * (q : ℝ) +
                    ∑ i ∈ Finset.range (jumpCount (fun m => ProbabilityTheory.arrival arrival m ω) (q : ℝ)),
                      claims i ω) =
                (0 + 1 * (u : ℝ) -
                  (0 + 0 * (u : ℝ) +
                    ∑ i ∈ Finset.range (jumpCount (fun m => ProbabilityTheory.arrival arrival m ω) (u : ℝ)),
                      claims i ω)) + ((q : ℝ) - (u : ℝ))
              rw [hJC_q]
              dsimp only [j]
              ring
            have hqr : -X ⟨(q : ℝ), by exact_mod_cast hq_nn⟩ ω ≤ x := hrat ⟨q, hq_nn, hq_le_n⟩
            have hq_lt_diff : (q : ℝ) < (u : ℝ) + (-X u ω - x) :=
              lt_of_lt_of_le hq2 (min_le_right _ _)
            linarith
      have hMeasR : MeasurableSet (({ω | -X (n : ℝ≥0) ω ≤ x} : Set Ω) ∩
          ⋂ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)},
            {ω | -X ⟨(q.1 : ℝ), by exact_mod_cast q.2.1⟩ ω ≤ x}) :=
        (measurableSet_le (hX_meas _).neg measurable_const).inter
          (MeasurableSet.iInter fun q => measurableSet_le (hX_meas _).neg measurable_const)
      exact hMeasR.nullMeasurableSet.congr hRat_eq.symm
    have hInter_lim := tendsto_measure_iInter_atTop (μ := P) hE_meas_nat
      (fun m n hmn => hE_anti (by exact_mod_cast hmn)) ⟨0, measure_ne_top P _⟩
    let R_compl : Set Ω := (ruinEvent arrival claims 1 x)ᶜ
    have hInter_eq : (⋂ n : ℕ, E (n : ℝ≥0)) =ᵐ[P] R_compl := by
      filter_upwards [hArrPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
      have hX0 : X 0 ω = 0 := by
        have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
          simpa [ProbabilityTheory.arrival] using hPosω 0
        have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
          have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
            rw [lt_jumpCount_iff hStrictω hTendstoω]; exact not_le.mpr hT0
          omega
        simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
          ProbabilityTheory.piecewisePath, hj0]
      change (ω ∈ ⋂ n : ℕ, E (n : ℝ≥0)) = (ω ∈ R_compl)
      dsimp only [R_compl]
      apply propext
      rw [Set.mem_iInter, Set.mem_compl_iff]
      simp only [E, Set.mem_ofPred_eq, ruinEvent, not_exists, not_and, not_lt]
      constructor
      · intro hall t _
        obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
        have hle := hall n t (by exact_mod_cast hn)
        have hSurp : riskSurplus arrival claims 1 x t ω = x + X t ω := by
          simp [X, riskSurplus]; ring
        linarith
      · intro hall n u _
        by_cases hu0 : u = 0
        · subst hu0; rw [hX0, neg_zero]; exact hx
        · have hge := hall u (pos_iff_ne_zero.mpr hu0)
          have hSurp : riskSurplus arrival claims 1 x u ω = x + X u ω := by
            simp [X, riskSurplus]; ring
          linarith
    have hRuin_nullMeas : NullMeasurableSet (ruinEvent arrival claims 1 x) P := by
      have hCompl_nm : NullMeasurableSet R_compl P :=
        (NullMeasurableSet.iInter hE_meas_nat).congr hInter_eq
      simpa [R_compl] using hCompl_nm.compl
    have hLimit_val : (P (⋂ n : ℕ, E (n : ℝ≥0))).toReal = 1 - ruinProbability P arrival claims 1 x := by
      rw [measure_congr hInter_eq]
      dsimp only [ruinProbability, R_compl]
      have hcompl : P (ruinEvent arrival claims 1 x)ᶜ = 1 - P (ruinEvent arrival claims 1 x) := by
        rw [measure_compl₀ hRuin_nullMeas (measure_ne_top P _), measure_univ]
      rw [hcompl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    have hNat_toReal : Tendsto (fun n : ℕ => (P (E (n : ℝ≥0))).toReal) atTop
        (𝓝 (1 - ruinProbability P arrival claims 1 x)) := by
      rw [← hLimit_val]
      exact (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp hInter_lim
    -- Sandwich E t between E (Nat.ceil t) and E (Nat.floor t)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun t : ℝ≥0 => (P (E ((Nat.ceil (t : ℝ) : ℕ) : ℝ≥0))).toReal)
      (h := fun t : ℝ≥0 => (P (E ((Nat.floor (t : ℝ) : ℕ) : ℝ≥0))).toReal) ?_ ?_ ?_ ?_
    · refine hNat_toReal.comp ?_
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(b : ℝ≥0), fun t ht => ?_⟩
      have h1 : (b : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      exact_mod_cast le_trans h1 (Nat.le_ceil (t : ℝ))
    · refine hNat_toReal.comp ?_
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(b : ℝ≥0), fun t ht => ?_⟩
      exact Nat.le_floor (by exact_mod_cast ht)
    · intro t
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (hE_anti (by
        rw [← NNReal.coe_le_coe]; exact Nat.le_ceil (t : ℝ))))
    · intro t
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (hE_anti (by
        rw [← NNReal.coe_le_coe]; exact Nat.floor_le t.2)))
  -- Step 5: Coupling W_t^(w) = W_t^(0) whenever w < X t, and P {X t ≤ w} → 0
  have hDiff_zero : Tendsto (fun t : ℝ≥0 => (P {ω | X t ω ≤ w}).toReal) atTop (𝓝 0) := by
    have hLim_ae : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 =>
        if X t ω ≤ w then (1 : ℝ) else 0) atTop (𝓝 0) := by
      filter_upwards [hX_tendsto_top] with ω hTopω
      rw [tendsto_atTop] at hTopω
      obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp (hTopω (w + 1))
      refine tendsto_atTop_of_eventually_const (i₀ := T0) fun t ht => ?_
      rw [if_neg (not_le.mpr (by linarith [hT0 t ht]))]
    have hEq_int : ∀ t : ℝ≥0, (P {ω | X t ω ≤ w}).toReal =
        ∫ ω, (if X t ω ≤ w then (1 : ℝ) else 0) ∂P := fun t => by
      have hInd : (fun ω => if X t ω ≤ w then (1 : ℝ) else 0) =
          ({ω | X t ω ≤ w}).indicator (fun _ => (1 : ℝ)) := by
        ext ω; by_cases h : X t ω ≤ w
        · simp [h]
        · simp [h]
      rw [hInd, integral_indicator (measurableSet_le (hX_meas t) measurable_const),
        setIntegral_const, smul_eq_mul, mul_one, Measure.real]
    simp_rw [hEq_int]
    have hDCT := tendsto_integral_filter_of_dominated_convergence
      (F := fun t : ℝ≥0 => fun ω : Ω => if X t ω ≤ w then (1 : ℝ) else 0)
      (f := fun _ : Ω => (0 : ℝ))
      (bound := fun _ : Ω => (1 : ℝ))
      (Filter.Eventually.of_forall fun t =>
        (Measurable.ite (measurableSet_le (hX_meas t) measurable_const)
          measurable_const measurable_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ω => by
        split_ifs <;> norm_num)
      (integrable_const 1)
      hLim_ae
    simpa using hDCT
  -- Sandwich (P {W_t^(w) ≤ x}).toReal using W_t^(0) ≤ W_t^(w) and W_t^(w) = W_t^(0) on {w < X t}
  rw [← hPK]
  have hLower : ∀ t : ℝ≥0,
      (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal - (P {ω | X t ω ≤ w}).toReal ≤
        (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal := by
    intro t
    have hSub_ae : ∀ᵐ ω ∂P,
        ω ∈ {ω | queueWorkload arrival claims 0 t ω ≤ x} →
          ω ∈ {ω | queueWorkload arrival claims w t ω ≤ x} ∪ {ω | X t ω ≤ w} := by
      filter_upwards [hClaimsPos] with ω hClmω hW0
      by_cases hXw : X t ω ≤ w
      · exact Or.inr hXw
      · left
        have hgt : w < X t ω := lt_of_not_ge hXw
        have hBdd : BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} := by
          refine ⟨(t : ℝ), ?_⟩
          rintro z ⟨s, hs, rfl⟩
          have hAgg : 0 ≤ aggregateClaims arrival claims s ω := by
            simp only [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]
            have : 0 ≤ ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)),
                claims i ω := Finset.sum_nonneg fun i _ => (hClmω i).le
            linarith
          have hsR : (s : ℝ) ≤ (t : ℝ) := hs
          simp only [X, riskSurplus]; linarith
        have hXt_le_sup : X t ω ≤ sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω} :=
          le_csSup hBdd ⟨t, le_rfl, rfl⟩
        have hWeq : queueWorkload arrival claims w t ω = queueWorkload arrival claims 0 t ω := by
          dsimp only [queueWorkload]
          rw [max_eq_right (le_trans hgt.le hXt_le_sup),
            max_eq_right (le_trans hw (le_trans hgt.le hXt_le_sup))]
        change queueWorkload arrival claims w t ω ≤ x
        rw [hWeq]; exact hW0
    have h1 : P {ω | queueWorkload arrival claims 0 t ω ≤ x} ≤
        P {ω | queueWorkload arrival claims w t ω ≤ x} + P {ω | X t ω ≤ w} :=
      le_trans (measure_mono_ae hSub_ae) (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P _, measure_ne_top P _⟩) h1
    rw [ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)] at h2
    linarith
  have hUpper : ∀ t : ℝ≥0,
      (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal ≤
        (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal := by
    intro t
    refine ENNReal.toReal_mono (measure_ne_top P _) (measure_mono fun ω hW => ?_)
    have hle : queueWorkload arrival claims 0 t ω ≤ queueWorkload arrival claims w t ω := by
      dsimp only [queueWorkload]
      have : max (0 : ℝ) (sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω}) ≤
          max w (sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω}) := max_le_max_right _ hw
      linarith
    exact le_trans hle hW
  have hLo_tend : Tendsto (fun t : ℝ≥0 =>
      (P {ω | queueWorkload arrival claims 0 t ω ≤ x}).toReal - (P {ω | X t ω ≤ w}).toReal)
      atTop (𝓝 (1 - ruinProbability P arrival claims 1 x)) := by
    simpa using hLim_zero.sub hDiff_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLo_tend hLim_zero hLower hUpper
