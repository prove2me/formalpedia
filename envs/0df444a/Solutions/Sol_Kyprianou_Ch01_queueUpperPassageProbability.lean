-- Prove2me | solution 1 for Kyprianou.Ch01.queueUpperPassageProbability
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T16:04:29.261578+00:00
-- url     : https://prove2.me/submissions/5b6b0edd-017d-4711-a813-342b87e71b0a

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_expMoment
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_indep_stationary
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Function
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

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

private lemma measurable_aggregateClaims_fixed
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (hArr : ∀ n, Measurable (arrival n))
    (hClm : ∀ n, Measurable (claims n))
    (t : ℝ≥0) :
    Measurable (aggregateClaims arrival claims t) := by
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
            · left
              have hmem := Nat.sInf_mem hne
              rwa [h0] at hmem
            · right
              intro n
              by_contra hgt
              exact hne ⟨n, lt_of_not_ge hgt⟩
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
            · have hmem := Nat.sInf_mem hne
              rwa [hj] at hmem
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
              have hlt' : n < j + 1 := lt_of_not_ge hlt
              exact not_lt_of_ge (hle n hlt') hn
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
    refine MeasurableSet.iUnion fun k => ?_
    exact (hJC (measurableSet_singleton k)).inter
      ((Finset.measurable_sum (Finset.range k) fun i _ => hClm i) hs)
  have hEq : aggregateClaims arrival claims t =
      fun ω => 0 + 0 * (t : ℝ) +
        ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
          claims i ω := by
    ext ω
    simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]
  rw [hEq]
  exact measurable_const.add hSumClm

private lemma measurable_riskSurplus_fixed
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (hArr : ∀ n, Measurable (arrival n))
    (hClm : ∀ n, Measurable (claims n))
    (t : ℝ≥0) :
    Measurable (riskSurplus arrival claims 1 0 t) := by
  have hEq : riskSurplus arrival claims 1 0 t =
      fun ω => 0 + 1 * (t : ℝ) - aggregateClaims arrival claims t ω := rfl
  rw [hEq]
  exact measurable_const.sub (measurable_aggregateClaims_fixed arrival claims hArr hClm t)

private noncomputable def stoppedExp
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (theta x : ℝ) : ℕ → Ω → ℝ
  | 0, ω => Real.exp (theta * X 0 ω)
  | K + 1, ω =>
      if ∀ j ≤ K, X (j • h) ω ≤ x then
        Real.exp (theta * X ((K + 1) • h) ω)
      else
        stoppedExp X h theta x K ω

private lemma stoppedExp_eq_exp_of_alive
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (theta x : ℝ)
    (K : ℕ) (ω : Ω) (halive : ∀ j < K, X (j • h) ω ≤ x) :
    stoppedExp X h theta x K ω = Real.exp (theta * X (K • h) ω) := by
  cases K with
  | zero => simp [stoppedExp]
  | succ k =>
      dsimp [stoppedExp]
      rw [if_pos (fun j hj => halive j (Nat.lt_succ_of_le hj))]

private lemma stoppedExp_step
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (theta x : ℝ) (K : ℕ) (ω : Ω) :
    stoppedExp X h theta x (K + 1) ω - stoppedExp X h theta x K ω =
      (if ∀ j ≤ K, X (j • h) ω ≤ x then Real.exp (theta * X (K • h) ω) else 0) *
        (Real.exp (theta * (X ((K + 1) • h) ω - X (K • h) ω)) - 1) := by
  by_cases halive : ∀ j ≤ K, X (j • h) ω ≤ x
  · have hK : stoppedExp X h theta x K ω = Real.exp (theta * X (K • h) ω) :=
      stoppedExp_eq_exp_of_alive X h theta x K ω (fun j hj => halive j hj.le)
    have hK1 : stoppedExp X h theta x (K + 1) ω = Real.exp (theta * X ((K + 1) • h) ω) := by
      dsimp [stoppedExp]; rw [if_pos halive]
    rw [hK1, hK, if_pos halive]
    have hExp : Real.exp (theta * X ((K + 1) • h) ω) =
        Real.exp (theta * X (K • h) ω) *
          Real.exp (theta * (X ((K + 1) • h) ω - X (K • h) ω)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    ring
  · have hK1 : stoppedExp X h theta x (K + 1) ω = stoppedExp X h theta x K ω := by
      dsimp [stoppedExp]; rw [if_neg halive]
    rw [hK1, if_neg halive]
    ring

private lemma stoppedExp_const_of_crossed
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (theta x : ℝ) (ω : Ω)
    {k0 K : ℕ} (hk0 : x < X (k0 • h) ω) (hK : k0 ≤ K) :
    stoppedExp X h theta x K ω = stoppedExp X h theta x k0 ω := by
  induction hK with
  | refl => rfl
  | @step m hm ih =>
      dsimp [stoppedExp]
      have hnot : ¬ (∀ j ≤ m, X (j • h) ω ≤ x) := fun hall => not_le_of_gt hk0 (hall k0 hm)
      rw [if_neg hnot, ih]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPos : F (Set.Iic (0 : ℝ)) = 0)
    (hIntegrable : Integrable (fun z : ℝ => z) F)
    (mu : ℝ) (hMean : (∫ z, z ∂F) = mu)
    (hOverload : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0) :
    ∀ x : ℝ, 0 < x →
      (P {ω | ∃ t : ℝ≥0, 0 < t ∧ x < riskSurplus arrival claims 1 0 t ω}).toReal =
        Real.exp (-theta * x) := by
  intro x hx
  set X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
  have hX_meas : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
    measurable_riskSurplus_fixed arrival claims hDriver.measurable_interarrival
      hDriver.measurable_mark t
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  -- Almost-sure path properties
  have hArrPos := hDriver.ae_interarrival_pos hrate
  have hStrict := hDriver.ae_strictMono_arrival hrate
  have hTendsto := hDriver.ae_tendsto_arrival hrate
  have hClaimsPos : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    have hlaw : P.map (claims n) = F := (hDriver.law_mark n).map_eq
    have hmeas : Measurable (claims n) := hDriver.measurable_mark n
    have hzero : P {ω | claims n ω ≤ 0} = 0 := by
      have hpre : {ω | claims n ω ≤ 0} = claims n ⁻¹' Set.Iic (0 : ℝ) := rfl
      rw [hpre, ← Measure.map_apply hmeas measurableSet_Iic, hlaw, hPos]
    rw [ae_iff]
    convert hzero using 2
    ext ω
    simp [not_lt]
  -- SLLN for interarrivals and claims -> X t → -∞ as t → ∞
  have hArr_int : Integrable (arrival 0) P := by
    have hlaw := hDriver.law_interarrival 0
    have h1 := integrable_id_expMeasure hrateR
    rw [← hlaw.map_eq] at h1
    exact h1.comp_aemeasurable (hDriver.measurable_interarrival 0).aemeasurable
  have hArr_mean : (∫ ω, arrival 0 ω ∂P) = (rate : ℝ)⁻¹ := by
    have hlaw := hDriver.law_interarrival 0
    have h1 := integral_id_expMeasure hrateR
    rw [← hlaw.map_eq] at h1
    have h2 : (∫ y : ℝ, y ∂(P.map (arrival 0))) = ∫ ω, arrival 0 ω ∂P :=
      integral_map (hDriver.measurable_interarrival 0).aemeasurable
        (aestronglyMeasurable_id (μ := P.map (arrival 0)))
    exact h2.symm.trans h1
  have hArr_indep : Pairwise ((· ⟂ᵢ[P] ·) on arrival) := fun i j hij =>
    (hDriver.indep.precomp Sum.inl_injective).indepFun hij
  have hArr_ident : ∀ i : ℕ, IdentDistrib (arrival i) (arrival 0) P P := fun i =>
    { aemeasurable_fst := (hDriver.measurable_interarrival i).aemeasurable
      aemeasurable_snd := (hDriver.measurable_interarrival 0).aemeasurable
      map_eq := by rw [(hDriver.law_interarrival i).map_eq, (hDriver.law_interarrival 0).map_eq] }
  have hArr_slln : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, arrival i ω) / (n : ℝ))
        atTop (𝓝 ((rate : ℝ)⁻¹)) := by
    simpa [hArr_mean] using strong_law_ae_real arrival hArr_int hArr_indep hArr_ident
  have hClm_int : Integrable (claims 0) P := by
    have hlaw := hDriver.law_mark 0
    rw [← hlaw.map_eq] at hIntegrable
    exact hIntegrable.comp_aemeasurable (hDriver.measurable_mark 0).aemeasurable
  have hClm_mean : (∫ ω, claims 0 ω ∂P) = mu := by
    have hlaw := hDriver.law_mark 0
    rw [← hlaw.map_eq] at hMean
    have h2 : (∫ y : ℝ, y ∂(P.map (claims 0))) = ∫ ω, claims 0 ω ∂P :=
      integral_map (hDriver.measurable_mark 0).aemeasurable
        (aestronglyMeasurable_id (μ := P.map (claims 0)))
    exact h2.symm.trans hMean
  have hClm_indep : Pairwise ((· ⟂ᵢ[P] ·) on claims) := fun i j hij =>
    (hDriver.indep.precomp Sum.inr_injective).indepFun hij
  have hClm_ident : ∀ i : ℕ, IdentDistrib (claims i) (claims 0) P P := fun i =>
    { aemeasurable_fst := (hDriver.measurable_mark i).aemeasurable
      aemeasurable_snd := (hDriver.measurable_mark 0).aemeasurable
      map_eq := by rw [(hDriver.law_mark i).map_eq, (hDriver.law_mark 0).map_eq] }
  have hClm_slln : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, claims i ω) / (n : ℝ))
        atTop (𝓝 mu) := by
    simpa [hClm_mean] using strong_law_ae_real claims hClm_int hClm_indep hClm_ident
  -- Pathwise: X (tGrid K) → -∞ under overload
  have hX_tendsto_neg : ∀ (h : ℝ≥0), 0 < h →
      ∀ᵐ ω ∂P, Tendsto (fun K : ℕ => X (K • h) ω) atTop atBot := by
    intro h hh
    have hhR : (0 : ℝ) < (h : ℝ) := NNReal.coe_pos.mpr hh
    filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos, hArr_slln, hClm_slln] with
      ω hPosω hStrictω hTendstoω hClaimsω hArrω hClmω
    have hGap : 0 < mu - (rate : ℝ)⁻¹ := by
      rw [sub_pos, ← mul_lt_mul_iff_right₀ hrateR, mul_inv_cancel₀ hrateR.ne']
      linarith
    set ε : ℝ := (mu - (rate : ℝ)⁻¹) / 3
    have hε : 0 < ε := by positivity
    -- (∑_{i < n+1} arrival i) / n → rate⁻¹
    have hArrSucc : Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.range (n + 1), arrival i ω) / (n : ℝ)) atTop (𝓝 ((rate : ℝ)⁻¹)) := by
      have h1 : Tendsto (fun n : ℕ =>
          ((∑ i ∈ Finset.range (n + 1), arrival i ω) / ((n + 1 : ℕ) : ℝ)) *
            (((n + 1 : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 ((rate : ℝ)⁻¹ * 1)) := by
        refine (hArrω.comp (tendsto_add_atTop_nat 1)).mul ?_
        have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ))⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        rw [add_zero] at hdiv
        refine hdiv.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp [hnR]
      rw [mul_one] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hn1]
    have hEvArr := hArrSucc.eventually (gt_mem_nhds (by linarith : (rate : ℝ)⁻¹ < (rate : ℝ)⁻¹ + ε))
    have hEvClm := hClmω.eventually (lt_mem_nhds (by linarith : mu - ε < mu))
    rw [Filter.eventually_atTop] at hEvArr hEvClm
    obtain ⟨N1, hN1⟩ := hEvArr
    obtain ⟨N2, hN2⟩ := hEvClm
    set T := fun n => ProbabilityTheory.arrival arrival n ω
    rw [Filter.tendsto_atBot]
    intro B
    rw [Filter.eventually_atTop]
    obtain ⟨N3, hN3⟩ := exists_nat_gt (max (-B / ε) 0)
    set N0 := max (max N1 N2) (max N3 1)
    obtain ⟨K0, hK0⟩ := exists_nat_gt (T N0 / (h : ℝ))
    refine ⟨K0, fun K hK => ?_⟩
    have hKh_gt : T N0 < (K : ℝ) * (h : ℝ) := by
      have h1 : T N0 / (h : ℝ) < (K : ℝ) := lt_of_lt_of_le hK0 (Nat.cast_le.mpr hK)
      rwa [div_lt_iff₀ hhR] at h1
    set n := jumpCount T ((K : ℝ) * (h : ℝ))
    have hn_gt : N0 < n := (lt_jumpCount_iff hStrictω hTendstoω N0 ((K : ℝ) * (h : ℝ))).mpr hKh_gt.le
    have hn_ge1 : 1 ≤ n := by omega
    have hnR_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hKh_lt_Tn : (K : ℝ) * (h : ℝ) < T n := by
      have hnot : ¬ (n < jumpCount T ((K : ℝ) * (h : ℝ))) := by omega
      rw [lt_jumpCount_iff hStrictω hTendstoω] at hnot
      exact lt_of_not_ge hnot
    have hTn_eq : T n = ∑ i ∈ Finset.range (n + 1), arrival i ω := rfl
    have hA_bd : T n / (n : ℝ) < (rate : ℝ)⁻¹ + ε := by
      rw [hTn_eq]; exact hN1 n (by omega)
    have hC_bd : mu - ε < (∑ i ∈ Finset.range n, claims i ω) / (n : ℝ) := hN2 n (by omega)
    have hA_mul : T n < (n : ℝ) * ((rate : ℝ)⁻¹ + ε) := by
      rwa [div_lt_iff₀ hnR_pos, mul_comm] at hA_bd
    have hC_mul : (n : ℝ) * (mu - ε) < ∑ i ∈ Finset.range n, claims i ω := by
      rwa [lt_div_iff₀ hnR_pos, mul_comm] at hC_bd
    have hX_val : X (K • h) ω = (K : ℝ) * (h : ℝ) - ∑ i ∈ Finset.range n, claims i ω := by
      have hcoe : ((K • h : ℝ≥0) : ℝ) = (K : ℝ) * (h : ℝ) := by simp [nsmul_eq_mul]
      simp only [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath, hcoe]
      change 0 + 1 * ((K : ℝ) * (h : ℝ)) -
        (0 + 0 * ((K : ℝ) * (h : ℝ)) + ∑ i ∈ Finset.range n, claims i ω) = _
      ring
    have hn_gt_N3 : -B / ε < (n : ℝ) := by
      have h1 : -B / ε ≤ max (-B / ε) 0 := le_max_left _ _
      have h2 : (N3 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr (by omega)
      linarith
    have hB_le : -B < (n : ℝ) * ε := by
      rwa [div_lt_iff₀ hε] at hn_gt_N3
    have hSub : (mu - ε) - ((rate : ℝ)⁻¹ + ε) = ε := by dsimp [ε]; ring
    have hX_le : X (K • h) ω ≤ -(n : ℝ) * ε := by
      rw [hX_val]
      nlinarith
    linarith
  -- Unit expectation of exp(theta * X h) for any h > 0
  have hExp_unit : ∀ (h : ℝ≥0), 0 < h →
      (∫ ω, Real.exp (theta * X h ω) ∂P) = 1 := by
    intro h hh
    have hAgg_nonneg : ∀ᵐ ω ∂P, 0 ≤ aggregateClaims arrival claims h ω := by
      filter_upwards [hClaimsPos] with ω hClaimsω
      simp only [aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath, zero_add, zero_mul]
      exact Finset.sum_nonneg fun i _ => (hClaimsω i).le
    have hAgg_int : Integrable
        (fun ω => Real.exp ((-theta) * aggregateClaims arrival claims h ω)) P := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (Real.continuous_exp.measurable.comp
          (measurable_const.mul (measurable_aggregateClaims_fixed arrival claims
            hDriver.measurable_interarrival hDriver.measurable_mark h))).aestronglyMeasurable
      · filter_upwards [hAgg_nonneg] with ω hnn
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        nlinarith
    have hMom := Kyprianou.Ch01.aggregateClaims_expMoment P arrival claims rate F
      hDriver hrate (-theta) h hh hAgg_int
    have hF_exp_int : Integrable (fun y : ℝ => Real.exp (-theta * y)) F := by
      simpa [neg_mul] using hMom.1
    have hInt_sub : (∫ y : ℝ, (1 - Real.exp (-theta * y)) ∂F) =
        1 - ∫ y : ℝ, Real.exp (-theta * y) ∂F := by
      rw [integral_sub (integrable_const 1) hF_exp_int, integral_const, probReal_univ,
        smul_eq_mul, mul_one]
    have hLap : theta + (rate : ℝ) * ((∫ y : ℝ, Real.exp (-theta * y) ∂F) - 1) = 0 := by
      have hr : theta - (rate : ℝ) * (∫ y : ℝ, (1 - Real.exp (-theta * y)) ∂F) = 0 := hRoot
      rw [hInt_sub] at hr
      linarith
    have hX_split : (fun ω => Real.exp (theta * X h ω)) =
        fun ω => Real.exp (theta * (h : ℝ)) *
          Real.exp ((-theta) * aggregateClaims arrival claims h ω) := by
      ext ω
      rw [← Real.exp_add]
      congr 1
      simp only [X, riskSurplus]
      ring
    rw [hX_split, integral_const_mul, hMom.2, ← Real.exp_add]
    have hZero : theta * (h : ℝ) +
        (rate : ℝ) * (h : ℝ) * ((∫ y : ℝ, Real.exp (-theta * y) ∂F) - 1) = 0 := by
      have : theta * (h : ℝ) + (rate : ℝ) * (h : ℝ) * ((∫ y : ℝ, Real.exp (-theta * y) ∂F) - 1) =
          (h : ℝ) * (theta + (rate : ℝ) * ((∫ y : ℝ, Real.exp (-theta * y) ∂F) - 1)) := by ring
      rw [this, hLap, mul_zero]
    rw [hZero, Real.exp_zero]
  -- Core grid bound for step size h > 0
  have hGrid_bound : ∀ (h : ℝ≥0), 0 < h →
      let E : Set Ω := ⋃ k : ℕ, {ω | x < X (k • h) ω}
      Real.exp (-theta * (x + (h : ℝ))) ≤ (P E).toReal ∧
        (P E).toReal ≤ Real.exp (-theta * x) := by
    intro h hh E
    have hE_meas : MeasurableSet E :=
      MeasurableSet.iUnion fun k => measurableSet_lt measurable_const (hX_meas (k • h))
    -- 1. Induction: ∫ stoppedExp X h theta x K = 1
    have hStop_int_and_eq : ∀ K : ℕ,
        Integrable (stoppedExp X h theta x K) P ∧
        (∫ ω, stoppedExp X h theta x K ω ∂P) = 1 := by
      intro K
      induction K with
      | zero =>
          have hX0_ae : ∀ᵐ ω ∂P, X 0 ω = 0 := by
            filter_upwards [hArrPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
            have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
              simpa [ProbabilityTheory.arrival] using hPosω 0
            have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
              have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
                rw [lt_jumpCount_iff hStrictω hTendstoω]
                exact not_le.mpr hT0
              omega
            simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
              ProbabilityTheory.piecewisePath, hj0]
          have hAE1 : stoppedExp X h theta x 0 =ᵐ[P] fun _ => (1 : ℝ) := by
            filter_upwards [hX0_ae] with ω h0
            simp [stoppedExp, h0]
          refine ⟨(integrable_const (1 : ℝ)).congr hAE1.symm, ?_⟩
          rw [integral_congr_ae hAE1, integral_const, probReal_univ, smul_eq_mul, mul_one]
      | succ K ih =>
          set U : Ω → ℝ := fun ω =>
            if ∀ j ≤ K, X (j • h) ω ≤ x then Real.exp (theta * X (K • h) ω) else 0
          set Δ : Ω → ℝ := fun ω => X ((K + 1) • h) ω - X (K • h) ω
          set V : Ω → ℝ := fun ω => Real.exp (theta * Δ ω) - 1
          have hStep : stoppedExp X h theta x (K + 1) =
              fun ω => stoppedExp X h theta x K ω + U ω * V ω := by
            ext ω
            have hs := stoppedExp_step X h theta x K ω
            linarith
          -- U is naturalSigma X (K • h)-measurable and bounded
          have hU_meas_nat : @Measurable Ω ℝ (naturalSigma X (K • h)) _ U := by
            have hXj_meas : ∀ j ≤ K, @Measurable Ω ℝ (naturalSigma X (K • h)) _ (X (j • h)) := by
              intro j hj
              have hle : j • h ≤ K • h := by
                rw [nsmul_eq_mul, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) h.2
              have hle_ms : MeasurableSpace.comap (X (j • h)) inferInstance ≤
                  naturalSigma X (K • h) := by
                dsimp [naturalSigma, PerfCorrMSQ.natFiltr]
                exact le_iSup₂_of_le (j • h) hle le_rfl
              exact (Measurable.of_comap_le hle_ms)
            have hSet_nat : @MeasurableSet Ω (naturalSigma X (K • h))
                {ω | ∀ j ≤ K, X (j • h) ω ≤ x} := by
              have hEq : {ω | ∀ j ≤ K, X (j • h) ω ≤ x} =
                  ⋂ j ∈ Finset.range (K + 1), X (j • h) ⁻¹' Set.Iic x := by
                ext ω; simp
              rw [hEq]
              exact @MeasurableSet.biInter Ω ℕ (naturalSigma X (K • h)) _ _
                (Finset.countable_toSet _) fun j hj =>
                  (hXj_meas j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) measurableSet_Iic
            have hExp_nat : @Measurable Ω ℝ (naturalSigma X (K • h)) _
                (fun ω => Real.exp (theta * X (K • h) ω)) :=
              Real.continuous_exp.measurable.comp
                ((@measurable_const ℝ Ω _ (naturalSigma X (K • h)) theta).mul (hXj_meas K le_rfl))
            exact Measurable.ite hSet_nat hExp_nat
              (@measurable_const ℝ Ω _ (naturalSigma X (K • h)) 0)
          have hU_meas : Measurable U := by
            have hSet : MeasurableSet {ω | ∀ j ≤ K, X (j • h) ω ≤ x} := by
              have hEq : {ω | ∀ j ≤ K, X (j • h) ω ≤ x} =
                  ⋂ j ∈ Finset.range (K + 1), {ω | X (j • h) ω ≤ x} := by
                ext ω; simp
              rw [hEq]
              exact MeasurableSet.biInter (Finset.countable_toSet _) fun j _ =>
                measurableSet_le (hX_meas (j • h)) measurable_const
            exact Measurable.ite hSet
              (Real.continuous_exp.measurable.comp (measurable_const.mul (hX_meas (K • h))))
              measurable_const
          have hU_bound : ∀ ω, ‖U ω‖ ≤ Real.exp (theta * x) := by
            intro ω
            dsimp [U]
            split_ifs with halive
            · rw [abs_of_nonneg (Real.exp_pos _).le]
              exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (halive K le_rfl) hTheta.le)
            · simp [(Real.exp_pos _).le]
          have hU_int : Integrable U P :=
            (integrable_const (Real.exp (theta * x))).mono' hU_meas.aestronglyMeasurable
              (Filter.Eventually.of_forall hU_bound)
          -- V is independent of U, bounded a.s., and has integral 0
          have hΔ_meas : Measurable Δ := (hX_meas ((K + 1) • h)).sub (hX_meas (K • h))
          have hV_meas : Measurable V :=
            (Real.continuous_exp.measurable.comp (measurable_const.mul hΔ_meas)).sub measurable_const
          have hΔ_le_ae : ∀ᵐ ω ∂P, Δ ω ≤ (h : ℝ) := by
            filter_upwards [hStrict, hTendsto, hClaimsPos] with ω hStrictω hTendstoω hClaimsω
            have hle_t : (K • h : ℝ≥0) ≤ ((K + 1) • h : ℝ≥0) := by
              rw [succ_nsmul]; exact le_self_add
            have hT_jc_mono : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                ((K • h : ℝ≥0) : ℝ) ≤
              jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                (((K + 1) • h : ℝ≥0) : ℝ) := by
              by_contra hgt
              have hlt : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                  (((K + 1) • h : ℝ≥0) : ℝ) <
                jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                  ((K • h : ℝ≥0) : ℝ) := lt_of_not_ge hgt
              set m := jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                (((K + 1) • h : ℝ≥0) : ℝ)
              have h1 : ProbabilityTheory.arrival arrival m ω ≤ ((K • h : ℝ≥0) : ℝ) :=
                (lt_jumpCount_iff hStrictω hTendstoω m ((K • h : ℝ≥0) : ℝ)).mp hlt
              have h2 : ¬ (m < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                  (((K + 1) • h : ℝ≥0) : ℝ)) := lt_irrefl _
              rw [lt_jumpCount_iff hStrictω hTendstoω] at h2
              have hleR : ((K • h : ℝ≥0) : ℝ) ≤ (((K + 1) • h : ℝ≥0) : ℝ) := hle_t
              exact h2 (le_trans h1 hleR)
            have hSum_mono :
                ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                  ((K • h : ℝ≥0) : ℝ)), claims i ω ≤
                ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
                  (((K + 1) • h : ℝ≥0) : ℝ)), claims i ω :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hT_jc_mono)
                (fun i _ _ => (hClaimsω i).le)
            have hcoe1 : ((K • h : ℝ≥0) : ℝ) = (K : ℝ) * (h : ℝ) := by simp [nsmul_eq_mul]
            have hcoe2 : (((K + 1) • h : ℝ≥0) : ℝ) = ((K + 1 : ℕ) : ℝ) * (h : ℝ) := by
              simp [nsmul_eq_mul]
            have hcoe_diff : (((K + 1) • h : ℝ≥0) : ℝ) = ((K • h : ℝ≥0) : ℝ) + (h : ℝ) := by
              rw [hcoe1, hcoe2]; push_cast; ring
            simp only [Δ, X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
              ProbabilityTheory.piecewisePath]
            linarith [hcoe_diff, hSum_mono]
          have hV_bound_ae : ∀ᵐ ω ∂P, ‖V ω‖ ≤ Real.exp (theta * (h : ℝ)) + 1 := by
            filter_upwards [hΔ_le_ae] with ω hle
            dsimp [V]
            have hexp_le : Real.exp (theta * Δ ω) ≤ Real.exp (theta * (h : ℝ)) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hTheta.le)
            have hexp_pos : 0 < Real.exp (theta * Δ ω) := Real.exp_pos _
            rw [abs_le]
            constructor <;> linarith
          have hV_int : Integrable V P :=
            (integrable_const (Real.exp (theta * (h : ℝ)) + 1)).mono'
              hV_meas.aestronglyMeasurable hV_bound_ae
          have hUV_int : Integrable (fun ω => U ω * V ω) P := by
            refine (integrable_const (Real.exp (theta * x) * (Real.exp (theta * (h : ℝ)) + 1))).mono'
              (hU_meas.mul hV_meas).aestronglyMeasurable ?_
            filter_upwards [hV_bound_ae] with ω hVbd
            rw [norm_mul]
            exact mul_le_mul (hU_bound ω) hVbd (norm_nonneg _) (Real.exp_pos _).le
          -- Independence and mean zero of V
          have hle_t : K • h ≤ (K + 1) • h := by
            rw [succ_nsmul]; exact le_self_add
          have hInc := Kyprianou.Ch01.riskSurplus_increment_indep_stationary P arrival claims
            rate hrate F hDriver 1 (K • h) ((K + 1) • h) hle_t
          have hIndep_UV : IndepFun U V P := by
            change Indep (MeasurableSpace.comap U inferInstance)
              (MeasurableSpace.comap V inferInstance) P
            have h1 : Indep (naturalSigma X (K • h)) (MeasurableSpace.comap Δ inferInstance) P :=
              hInc.1.symm
            have hU_le : MeasurableSpace.comap U inferInstance ≤ naturalSigma X (K • h) :=
              hU_meas_nat.comap_le
            have hV_le : MeasurableSpace.comap V inferInstance ≤
                MeasurableSpace.comap Δ inferInstance := by
              have hV_comp : V = (fun z : ℝ => Real.exp (theta * z) - 1) ∘ Δ := rfl
              rw [hV_comp, ← MeasurableSpace.comap_comp]
              exact MeasurableSpace.comap_mono
                ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).sub
                  measurable_const).comap_le
            exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h1 hU_le) hV_le
          have hSub_eq : (K + 1) • h - K • h = h := by
            rw [succ_nsmul, add_tsub_cancel_left]
          have hV_mean : (∫ ω, V ω ∂P) = 0 := by
            have hExpΔ : (∫ ω, Real.exp (theta * Δ ω) ∂P) = 1 := by
              have h1 : (∫ z : ℝ, Real.exp (theta * z) ∂(P.map Δ)) =
                  ∫ ω, Real.exp (theta * Δ ω) ∂P :=
                integral_map hΔ_meas.aemeasurable
                  (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
              have h2 : (∫ z : ℝ, Real.exp (theta * z) ∂(P.map (X h))) =
                  ∫ ω, Real.exp (theta * X h ω) ∂P :=
                integral_map (hX_meas h).aemeasurable
                  (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
              have hmap : P.map Δ = P.map (X h) := by
                have h2' := hInc.2
                rw [hSub_eq] at h2'
                exact h2'
              rw [← h1, hmap, h2, hExp_unit h hh]
            have hExpΔ_int : Integrable (fun ω => Real.exp (theta * Δ ω)) P := by
              have hEq : (fun ω => Real.exp (theta * Δ ω)) = fun ω => V ω + 1 := by
                ext ω; dsimp [V]; ring
              rw [hEq]
              exact hV_int.add (integrable_const 1)
            change (∫ ω, (Real.exp (theta * Δ ω) - 1) ∂P) = 0
            rw [integral_sub hExpΔ_int (integrable_const 1), hExpΔ, integral_const, probReal_univ,
              smul_eq_mul, mul_one, sub_self]
          have hInt_UV : (∫ ω, U ω * V ω ∂P) = 0 := by
            rw [hIndep_UV.integral_fun_mul_eq_mul_integral hU_meas.aestronglyMeasurable
              hV_meas.aestronglyMeasurable, hV_mean, mul_zero]
          refine ⟨ih.1.add hUV_int |>.congr (Filter.EventuallyEq.of_eq hStep.symm), ?_⟩
          rw [hStep, integral_add ih.1 hUV_int, ih.2, hInt_UV, add_zero]
    -- 2. Limit Mlim as K → ∞ via dominated convergence
    classical
    let Mlim : Ω → ℝ := fun ω =>
      if hEx : ∃ k : ℕ, x < X (k • h) ω then
        Real.exp (theta * X ((Nat.find hEx) • h) ω)
      else 0
    have hStop_meas : ∀ K : ℕ, Measurable (stoppedExp X h theta x K) := fun K => by
      induction K with
      | zero =>
          exact Real.continuous_exp.measurable.comp (measurable_const.mul (hX_meas 0))
      | succ k ih =>
          have hSet : MeasurableSet {ω | ∀ j ≤ k, X (j • h) ω ≤ x} := by
            have hEq : {ω | ∀ j ≤ k, X (j • h) ω ≤ x} =
                ⋂ j ∈ Finset.range (k + 1), {ω | X (j • h) ω ≤ x} := by
              ext ω; simp
            rw [hEq]
            exact MeasurableSet.biInter (Finset.countable_toSet _) fun j _ =>
              measurableSet_le (hX_meas (j • h)) measurable_const
          exact Measurable.ite hSet
            (Real.continuous_exp.measurable.comp (measurable_const.mul (hX_meas ((k + 1) • h))))
            ih
    have hPath_good : ∀ᵐ ω ∂P,
        (∀ K : ℕ, ‖stoppedExp X h theta x K ω‖ ≤ Real.exp (theta * (x + (h : ℝ)))) ∧
        Tendsto (fun K : ℕ => stoppedExp X h theta x K ω) atTop (𝓝 (Mlim ω)) ∧
        (ω ∈ E → Real.exp (theta * x) ≤ Mlim ω ∧ Mlim ω ≤ Real.exp (theta * (x + (h : ℝ)))) ∧
        (ω ∉ E → Mlim ω = 0) := by
      filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos, hX_tendsto_neg h hh] with
        ω hPosω hStrictω hTendstoω hClaimsω hXnegω
      have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
        simpa [ProbabilityTheory.arrival] using hPosω 0
      have hX0 : X 0 ω = 0 := by
        have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
          have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
            rw [lt_jumpCount_iff hStrictω hTendstoω]
            exact not_le.mpr hT0
          omega
        simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
          ProbabilityTheory.piecewisePath, hj0]
      have hInc_le : ∀ k : ℕ, X ((k + 1) • h) ω ≤ X (k • h) ω + (h : ℝ) := by
        intro k
        have hle_t : (k • h : ℝ≥0) ≤ ((k + 1) • h : ℝ≥0) := by
          rw [succ_nsmul]; exact le_self_add
        have hT_jc_mono : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
            ((k • h : ℝ≥0) : ℝ) ≤
          jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
            (((k + 1) • h : ℝ≥0) : ℝ) := by
          by_contra hgt
          have hlt := lt_of_not_ge hgt
          set m := jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
            (((k + 1) • h : ℝ≥0) : ℝ)
          have h1 : ProbabilityTheory.arrival arrival m ω ≤ ((k • h : ℝ≥0) : ℝ) :=
            (lt_jumpCount_iff hStrictω hTendstoω m ((k • h : ℝ≥0) : ℝ)).mp hlt
          have h2 : ¬ (m < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
              (((k + 1) • h : ℝ≥0) : ℝ)) := lt_irrefl _
          rw [lt_jumpCount_iff hStrictω hTendstoω] at h2
          have hleR : ((k • h : ℝ≥0) : ℝ) ≤ (((k + 1) • h : ℝ≥0) : ℝ) := hle_t
          exact h2 (le_trans h1 hleR)
        have hSum_mono := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hT_jc_mono)
          (fun i _ _ => (hClaimsω i).le)
        have hcoe1 : ((k • h : ℝ≥0) : ℝ) = (k : ℝ) * (h : ℝ) := by simp [nsmul_eq_mul]
        have hcoe2 : (((k + 1) • h : ℝ≥0) : ℝ) = ((k + 1 : ℕ) : ℝ) * (h : ℝ) := by
          simp [nsmul_eq_mul]
        simp only [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
          ProbabilityTheory.piecewisePath]
        have hcoe_diff : (((k + 1) • h : ℝ≥0) : ℝ) = ((k • h : ℝ≥0) : ℝ) + (h : ℝ) := by
          rw [hcoe1, hcoe2]; push_cast; ring
        linarith [hcoe_diff, hSum_mono]
      have hBd : ∀ K : ℕ, ‖stoppedExp X h theta x K ω‖ ≤ Real.exp (theta * (x + (h : ℝ))) := by
        intro K
        induction K with
        | zero =>
            simp only [stoppedExp, hX0, mul_zero, Real.exp_zero, norm_one]
            exact Real.one_le_exp (mul_nonneg hTheta.le (by linarith [h.2]))
        | succ k ih =>
            dsimp [stoppedExp]
            split_ifs with halive
            · rw [abs_of_nonneg (Real.exp_pos _).le]
              apply Real.exp_le_exp.mpr
              apply mul_le_mul_of_nonneg_left _ hTheta.le
              linarith [hInc_le k, halive k le_rfl]
            · exact ih
      refine ⟨hBd, ?_, ?_, ?_⟩
      · by_cases hEx : ∃ k : ℕ, x < X (k • h) ω
        · set k0 := Nat.find hEx
          have hk0_gt : x < X (k0 • h) ω := Nat.find_spec hEx
          have hk0_min : ∀ j < k0, X (j • h) ω ≤ x := fun j hj =>
            le_of_not_gt (Nat.find_min hEx hj)
          have hVal : stoppedExp X h theta x k0 ω = Real.exp (theta * X (k0 • h) ω) :=
            stoppedExp_eq_exp_of_alive X h theta x k0 ω hk0_min
          have hMlim_eq : Mlim ω = Real.exp (theta * X (k0 • h) ω) := by
            dsimp [Mlim]; rw [dif_pos hEx]
          rw [hMlim_eq]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop k0] with K hK
          rw [stoppedExp_const_of_crossed X h theta x ω hk0_gt hK, hVal]
        · have hMlim_eq : Mlim ω = 0 := by dsimp [Mlim]; rw [dif_neg hEx]
          rw [hMlim_eq]
          have hall : ∀ k : ℕ, X (k • h) ω ≤ x := fun k => le_of_not_gt fun hgt => hEx ⟨k, hgt⟩
          have hEq : ∀ K : ℕ, stoppedExp X h theta x K ω = Real.exp (theta * X (K • h) ω) :=
            fun K => stoppedExp_eq_exp_of_alive X h theta x K ω (fun j _ => hall j)
          simp_rw [hEq]
          exact Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot hTheta hXnegω)
      · intro hmem
        have hEx : ∃ k : ℕ, x < X (k • h) ω := by simpa [E] using hmem
        set k0 := Nat.find hEx
        have hk0_gt : x < X (k0 • h) ω := Nat.find_spec hEx
        have hk0_pos : 0 < k0 := by
          by_contra h0
          have hk00 : k0 = 0 := Nat.eq_zero_of_not_pos h0
          rw [hk00, zero_smul, hX0] at hk0_gt
          linarith
        have hk0_prev : X ((k0 - 1) • h) ω ≤ x :=
          le_of_not_gt (Nat.find_min hEx (Nat.sub_lt hk0_pos Nat.zero_lt_one))
        have hk0_le : X (k0 • h) ω ≤ x + (h : ℝ) := by
          have hstep := hInc_le (k0 - 1)
          rw [Nat.sub_add_cancel hk0_pos] at hstep
          linarith
        have hMlim_eq : Mlim ω = Real.exp (theta * X (k0 • h) ω) := by
          dsimp [Mlim]; rw [dif_pos hEx]
        rw [hMlim_eq]
        constructor
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk0_gt.le hTheta.le)
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk0_le hTheta.le)
      · intro hnot
        have hEx : ¬ ∃ k : ℕ, x < X (k • h) ω := by simpa [E] using hnot
        dsimp [Mlim]
        rw [dif_neg hEx]
    have hDCT : Tendsto (fun K : ℕ => ∫ ω, stoppedExp X h theta x K ω ∂P)
        atTop (𝓝 (∫ ω, Mlim ω ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => Real.exp (theta * (x + (h : ℝ))))
        (fun K => (hStop_meas K).aestronglyMeasurable)
        (integrable_const _)
        (fun K => hPath_good.mono fun ω hω => hω.1 K)
        (hPath_good.mono fun ω hω => hω.2.1)
    have hMlim_int_eq_one : (∫ ω, Mlim ω ∂P) = 1 := by
      have hconst : Tendsto (fun K : ℕ => ∫ ω, stoppedExp X h theta x K ω ∂P) atTop (𝓝 1) := by
        simp_rw [(hStop_int_and_eq _).2]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique hDCT hconst
    have hMlim_aem : AEStronglyMeasurable Mlim P :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun K => (hStop_meas K).aestronglyMeasurable)
        (hPath_good.mono fun ω hω => hω.2.1)
    have hMlim_int : Integrable Mlim P :=
      (integrable_const (Real.exp (theta * (x + (h : ℝ))))).mono' hMlim_aem
        (hPath_good.mono fun ω hω => by
          by_cases hm : ω ∈ E
          · have hbd := hω.2.2.1 hm
            rw [Real.norm_of_nonneg (le_trans (Real.exp_pos _).le hbd.1)]
            exact hbd.2
          · rw [hω.2.2.2 hm, norm_zero]
            exact (Real.exp_pos _).le)
    have hLower_ae : (E.indicator (fun _ => Real.exp (theta * x))) ≤ᵐ[P] Mlim :=
      hPath_good.mono fun ω hω => by
        by_cases hm : ω ∈ E
        · rw [Set.indicator_of_mem hm]; exact (hω.2.2.1 hm).1
        · rw [Set.indicator_of_notMem hm, hω.2.2.2 hm]
    have hUpper_ae : Mlim ≤ᵐ[P] (E.indicator (fun _ => Real.exp (theta * (x + (h : ℝ))))) :=
      hPath_good.mono fun ω hω => by
        by_cases hm : ω ∈ E
        · rw [Set.indicator_of_mem hm]; exact (hω.2.2.1 hm).2
        · rw [Set.indicator_of_notMem hm, hω.2.2.2 hm]
    have hLow_int : Integrable (E.indicator (fun _ => Real.exp (theta * x))) P :=
      (integrable_const _).indicator hE_meas
    have hUp_int : Integrable (E.indicator (fun _ => Real.exp (theta * (x + (h : ℝ))))) P :=
      (integrable_const _).indicator hE_meas
    have hLow_le : Real.exp (theta * x) * (P E).toReal ≤ 1 := by
      have h1 := integral_mono_ae hLow_int hMlim_int hLower_ae
      rw [integral_indicator_const _ hE_meas, smul_eq_mul, mul_comm, Measure.real,
        hMlim_int_eq_one] at h1
      exact h1
    have hUp_ge : 1 ≤ Real.exp (theta * (x + (h : ℝ))) * (P E).toReal := by
      have h1 := integral_mono_ae hMlim_int hUp_int hUpper_ae
      rw [integral_indicator_const _ hE_meas, smul_eq_mul, mul_comm, Measure.real,
        hMlim_int_eq_one] at h1
      exact h1
    constructor
    · have hmul : Real.exp (-theta * (x + (h : ℝ))) * Real.exp (theta * (x + (h : ℝ))) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc Real.exp (-theta * (x + (h : ℝ)))
          = Real.exp (-theta * (x + (h : ℝ))) * 1 := (mul_one _).symm
        _ ≤ Real.exp (-theta * (x + (h : ℝ))) * (Real.exp (theta * (x + (h : ℝ))) * (P E).toReal) :=
            mul_le_mul_of_nonneg_left hUp_ge (Real.exp_pos _).le
        _ = (Real.exp (-theta * (x + (h : ℝ))) * Real.exp (theta * (x + (h : ℝ)))) * (P E).toReal := by ring
        _ = (P E).toReal := by rw [hmul, one_mul]
    · have hmul : Real.exp (-theta * x) * Real.exp (theta * x) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc (P E).toReal
          = (Real.exp (-theta * x) * Real.exp (theta * x)) * (P E).toReal := by rw [hmul, one_mul]
        _ = Real.exp (-theta * x) * (Real.exp (theta * x) * (P E).toReal) := by ring
        _ ≤ Real.exp (-theta * x) * 1 := mul_le_mul_of_nonneg_left hLow_le (Real.exp_pos _).le
        _ = Real.exp (-theta * x) := mul_one _
  -- 3. Take dyadic grid h_m = 2^(-m) and let m → ∞
  let hm : ℕ → ℝ≥0 := fun m => ((2 : ℝ≥0)⁻¹) ^ m
  have hm_pos : ∀ m : ℕ, 0 < hm m := fun m => pow_pos (by positivity) m
  let Em : ℕ → Set Ω := fun m => ⋃ k : ℕ, {ω | x < X (k • hm m) ω}
  have hEm_mono : Monotone Em := by
    intro m₁ m₂ hmle ω hω
    rw [Set.mem_iUnion] at hω ⊢
    obtain ⟨k, hk⟩ := hω
    refine ⟨k * 2 ^ (m₂ - m₁), ?_⟩
    have hEq : (k * 2 ^ (m₂ - m₁)) • hm m₂ = k • hm m₁ := by
      apply NNReal.eq
      simp only [hm, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
        NNReal.coe_inv, NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have hpow : ((2 : ℝ)⁻¹) ^ m₂ = ((2 : ℝ)⁻¹) ^ m₁ * ((2 : ℝ)⁻¹) ^ (m₂ - m₁) := by
        rw [← pow_add, Nat.add_sub_cancel' hmle]
      rw [hpow]
      have hcancel : (2 : ℝ) ^ (m₂ - m₁) * ((2 : ℝ)⁻¹) ^ (m₂ - m₁) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
      calc ((k : ℝ) * (2 : ℝ) ^ (m₂ - m₁)) * (((2 : ℝ)⁻¹) ^ m₁ * ((2 : ℝ)⁻¹) ^ (m₂ - m₁))
          = (k : ℝ) * ((2 : ℝ)⁻¹) ^ m₁ * ((2 : ℝ) ^ (m₂ - m₁) * ((2 : ℝ)⁻¹) ^ (m₂ - m₁)) := by ring
        _ = (k : ℝ) * ((2 : ℝ)⁻¹) ^ m₁ := by rw [hcancel, mul_one]
    rwa [hEq]
  have hUnion_eq : {ω | ∃ t : ℝ≥0, 0 < t ∧ x < X t ω} =ᵐ[P] ⋃ m : ℕ, Em m := by
    filter_upwards [hArrPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
    change (∃ t : ℝ≥0, 0 < t ∧ x < X t ω) = (ω ∈ ⋃ m : ℕ, Em m)
    apply propext
    constructor
    · rintro ⟨t, ht_pos, hxt⟩
      set T := fun n => ProbabilityTheory.arrival arrival n ω
      set j := jumpCount T (t : ℝ)
      have hlt_next : (t : ℝ) < T j := by
        have hnot : ¬ (j < jumpCount T (t : ℝ)) := lt_irrefl _
        rw [lt_jumpCount_iff hStrictω hTendstoω] at hnot
        exact lt_of_not_ge hnot
      have hgap : 0 < T j - (t : ℝ) := sub_pos.mpr hlt_next
      have hpow0 : Tendsto (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hEv := hpow0.eventually (gt_mem_nhds hgap)
      rw [Filter.eventually_atTop] at hEv
      obtain ⟨m, hm_lt⟩ := hEv
      have hstep_lt : ((hm m : ℝ≥0) : ℝ) < T j - (t : ℝ) := by
        simpa [hm] using hm_lt m le_rfl
      have hstep_pos : (0 : ℝ) < ((hm m : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (hm_pos m)
      set k : ℕ := Nat.floor ((t : ℝ) / ((hm m : ℝ≥0) : ℝ)) + 1
      have hkt_gt : (t : ℝ) < (k : ℝ) * ((hm m : ℝ≥0) : ℝ) := by
        have h1 : (t : ℝ) / ((hm m : ℝ≥0) : ℝ) < (k : ℝ) := by
          dsimp [k]; push_cast; exact Nat.lt_floor_add_one _
        rwa [div_lt_iff₀ hstep_pos] at h1
      have hkt_lt : (k : ℝ) * ((hm m : ℝ≥0) : ℝ) < T j := by
        have h1 : ((Nat.floor ((t : ℝ) / ((hm m : ℝ≥0) : ℝ)) : ℕ) : ℝ) ≤
            (t : ℝ) / ((hm m : ℝ≥0) : ℝ) :=
          Nat.floor_le (div_nonneg t.2 hstep_pos.le)
        have h2 : ((Nat.floor ((t : ℝ) / ((hm m : ℝ≥0) : ℝ)) : ℕ) : ℝ) *
            ((hm m : ℝ≥0) : ℝ) ≤ (t : ℝ) := (le_div_iff₀ hstep_pos).mp h1
        have h3 : (k : ℝ) * ((hm m : ℝ≥0) : ℝ) =
            ((Nat.floor ((t : ℝ) / ((hm m : ℝ≥0) : ℝ)) : ℕ) : ℝ) * ((hm m : ℝ≥0) : ℝ) +
              ((hm m : ℝ≥0) : ℝ) := by
          dsimp [k]; push_cast; ring
        linarith
      have hjk : jumpCount T ((k • hm m : ℝ≥0) : ℝ) = j := by
        have hcoe : ((k • hm m : ℝ≥0) : ℝ) = (k : ℝ) * ((hm m : ℝ≥0) : ℝ) := by
          simp [nsmul_eq_mul]
        rw [hcoe]
        have hle_j : ¬ (j < jumpCount T ((k : ℝ) * ((hm m : ℝ≥0) : ℝ))) := by
          rw [lt_jumpCount_iff hStrictω hTendstoω]
          exact not_le.mpr hkt_lt
        cases hj : j with
        | zero => omega
        | succ i =>
            have hi_lt : i < jumpCount T (t : ℝ) := by omega
            have hTi_le : T i ≤ (t : ℝ) := (lt_jumpCount_iff hStrictω hTendstoω i (t : ℝ)).mp hi_lt
            have hi_lt' : i < jumpCount T ((k : ℝ) * ((hm m : ℝ≥0) : ℝ)) :=
              (lt_jumpCount_iff hStrictω hTendstoω i _).mpr (le_trans hTi_le hkt_gt.le)
            omega
      have hX_gt : x < X (k • hm m) ω := by
        have hcoe : ((k • hm m : ℝ≥0) : ℝ) = (k : ℝ) * ((hm m : ℝ≥0) : ℝ) := by
          simp [nsmul_eq_mul]
        have hval : X (k • hm m) ω = X t ω + ((k : ℝ) * ((hm m : ℝ≥0) : ℝ) - (t : ℝ)) := by
          simp only [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath]
          change 0 + 1 * ((k • hm m : ℝ≥0) : ℝ) -
            (0 + 0 * ((k • hm m : ℝ≥0) : ℝ) + ∑ i ∈ Finset.range (jumpCount T ((k • hm m : ℝ≥0) : ℝ)), claims i ω) =
            0 + 1 * (t : ℝ) -
            (0 + 0 * (t : ℝ) + ∑ i ∈ Finset.range j, claims i ω) + ((k : ℝ) * ((hm m : ℝ≥0) : ℝ) - (t : ℝ))
          rw [hjk, hcoe]
          ring
        rw [hval]
        linarith
      rw [Set.mem_iUnion]
      refine ⟨m, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨k, hX_gt⟩
    · intro hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨m, hm_mem⟩ := hmem
      rw [Set.mem_iUnion] at hm_mem
      obtain ⟨k, hk_mem⟩ := hm_mem
      have hk_pos : 0 < k := by
        by_contra h0
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos h0
        have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
          simpa [ProbabilityTheory.arrival] using hPosω 0
        have hj0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0 = 0 := by
          have hnot : ¬ (0 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) 0) := by
            rw [lt_jumpCount_iff hStrictω hTendstoω]
            exact not_le.mpr hT0
          omega
        have hX0 : X 0 ω = 0 := by
          simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hj0]
        change x < X (k • hm m) ω at hk_mem
        rw [hk0, zero_smul, hX0] at hk_mem
        linarith
      have ht_pos : 0 < k • hm m := by
        rw [nsmul_eq_mul]
        exact mul_pos (Nat.cast_pos.mpr hk_pos) (hm_pos m)
      exact ⟨k • hm m, ht_pos, hk_mem⟩
  have hP_tendsto : Tendsto (fun m : ℕ => (P (Em m)).toReal) atTop
      (𝓝 (P (⋃ m : ℕ, Em m)).toReal) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hEm_mono
    exact (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp h1
  have hLow_tendsto : Tendsto (fun m : ℕ => Real.exp (-theta * (x + ((hm m : ℝ≥0) : ℝ))))
      atTop (𝓝 (Real.exp (-theta * x))) := by
    have hpow0 : Tendsto (fun m : ℕ => ((hm m : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
      simpa [hm] using h0
    have harg : Tendsto (fun m : ℕ => -theta * (x + ((hm m : ℝ≥0) : ℝ))) atTop
        (𝓝 (-theta * (x + 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add hpow0)
    rw [add_zero] at harg
    exact Real.continuous_exp.continuousAt.tendsto.comp harg
  have hSqueeze : Tendsto (fun m : ℕ => (P (Em m)).toReal) atTop (𝓝 (Real.exp (-theta * x))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hLow_tendsto tendsto_const_nhds
      (fun m => (hGrid_bound (hm m) (hm_pos m)).1)
      (fun m => (hGrid_bound (hm m) (hm_pos m)).2)
  have hEq_lim : (P (⋃ m : ℕ, Em m)).toReal = Real.exp (-theta * x) :=
    tendsto_nhds_unique hP_tendsto hSqueeze
  rw [measure_congr hUnion_eq, hEq_lim]
