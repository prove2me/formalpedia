-- Prove2me | solution 1 for Kyprianou.Ch01.mg1UnboundedLimsup
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T16:17:13.675838+00:00
-- url     : https://prove2.me/submissions/33e0680c-1ef9-4356-9afc-c4c9d3cf2c67

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_indep_stationary
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false
universe u

private lemma measurable_riskSurplus_mg1
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
    (hheavy : 1 ≤ (rate : ℝ) * mu) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | ∀ M : ℝ, ∀ T : ℝ≥0,
        ∃ t : ℝ≥0, T ≤ t ∧
          M < queueWorkload arrival claims w t ω}).toReal = 1 := by
  intro w hw
  set X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
  have hX_meas : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
    measurable_riskSurplus_mg1 arrival claims hd.measurable_interarrival hd.measurable_mark t
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  have hArrPos := hd.ae_interarrival_pos hrate
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
    ext ω; simp [not_lt]
  -- Step 1: Existence of δ > 0 with F (Ioi δ) > 0
  have hF_Ioi_pos : ∃ δ : ℝ, 0 < δ ∧ 0 < F (Set.Ioi δ) := by
    by_contra hall
    push Not at hall
    have hUnion : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1)) := by
      ext z
      simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / z)
        refine ⟨n, ?_⟩
        have hn1 : 1 / z < (n : ℝ) + 1 := by linarith
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hz] at hn1
        linarith
      · rintro ⟨n, hn⟩
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hZero : F (Set.Ioi (0 : ℝ)) = 0 := by
      rw [hUnion]
      refine measure_iUnion_null fun n => ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact nonpos_iff_eq_zero.mp (hall _ hpos)
    have hCompl : (Set.Iic (0 : ℝ))ᶜ = Set.Ioi (0 : ℝ) := Set.compl_Iic
    have h1 : F Set.univ = 0 := by
      rw [← Set.union_compl_self (Set.Iic (0 : ℝ)), hCompl]
      have hle : F (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)) ≤ F (Set.Iic (0 : ℝ)) + F (Set.Ioi (0 : ℝ)) :=
        measure_union_le _ _
      rw [hclaimpos, hZero, add_zero] at hle
      exact nonpos_iff_eq_zero.mp hle
    rw [measure_univ] at h1
    exact one_ne_zero h1
  obtain ⟨δ, hδ_pos, hFδ_pos⟩ := hF_Ioi_pos
  -- Step 2: For any M : ℝ, P {ω | M < -(X 1 ω)} > 0
  have hDrop_pos : ∀ M : ℝ, 0 < P {ω | M < -(X 1 ω)} := by
    intro M
    obtain ⟨N0, hN0⟩ := exists_nat_gt ((max (M + 1) 0) / δ)
    set N : ℕ := N0 + 1
    have hN_pos : 0 < N := Nat.succ_pos N0
    have hNR_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    have hNδ : M + 1 < (N : ℝ) * δ := by
      have h1 : (max (M + 1) 0) / δ < (N : ℝ) := by
        have : (N0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self N0
        linarith
      rw [div_lt_iff₀ hδ_pos] at h1
      have h2 : M + 1 ≤ max (M + 1) 0 := le_max_left _ _
      linarith
    set S : Finset (ℕ ⊕ ℕ) :=
      (Finset.range N).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.range N).map ⟨Sum.inr, Sum.inr_injective⟩
    let E : ℕ ⊕ ℕ → Set ℝ := Sum.elim (fun _ => Set.Iic (1 / (N : ℝ))) (fun _ => Set.Ioi δ)
    set B : Set Ω := ⋂ j ∈ S, Sum.elim arrival claims j ⁻¹' E j
    have hE_meas : ∀ j, MeasurableSet (E j) := fun j => by
      cases j with
      | inl _ => exact measurableSet_Iic
      | inr _ => exact measurableSet_Ioi
    have hPB_eq : P B = ∏ j ∈ S, P (Sum.elim arrival claims j ⁻¹' E j) := by
      refine hd.indep.meas_biInter (S := S) (s := fun j => Sum.elim arrival claims j ⁻¹' E j) ?_
      intro j _
      exact ⟨E j, hE_meas j, rfl⟩
    have hFactor_pos : ∀ j ∈ S, 0 < P (Sum.elim arrival claims j ⁻¹' E j) := by
      intro j _
      cases j with
      | inl i =>
          change 0 < P (arrival i ⁻¹' Set.Iic (1 / (N : ℝ)))
          rw [← Measure.map_apply (hd.measurable_interarrival i) measurableSet_Iic,
            (hd.law_interarrival i).map_eq]
          have : IsProbabilityMeasure (expMeasure (rate : ℝ)) := isProbabilityMeasure_expMeasure hrateR
          have h1 : (expMeasure (rate : ℝ) (Set.Iic (1 / (N : ℝ)))).toReal =
              cdf (expMeasure (rate : ℝ)) (1 / (N : ℝ)) := by
            rw [cdf_eq_real, Measure.real]
          rw [cdf_expMeasure_eq hrateR, if_pos (by positivity)] at h1
          have htoReal_pos : 0 < (expMeasure (rate : ℝ) (Set.Iic (1 / (N : ℝ)))).toReal := by
            rw [h1]
            have hexp_lt : Real.exp (-((rate : ℝ) * (1 / (N : ℝ)))) < 1 :=
              Real.exp_lt_one_iff.mpr (by
                have : 0 < (rate : ℝ) * (1 / (N : ℝ)) := by positivity
                linarith)
            linarith
          exact pos_iff_ne_zero.mpr (fun hz => by rw [hz] at htoReal_pos; simp at htoReal_pos)
      | inr i =>
          change 0 < P (claims i ⁻¹' Set.Ioi δ)
          rw [← Measure.map_apply (hd.measurable_mark i) measurableSet_Ioi,
            (hd.law_mark i).map_eq]
          exact hFδ_pos
    have hPB_pos : 0 < P B := by
      rw [hPB_eq]
      exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j hj => ne_of_gt (hFactor_pos j hj))
    have hSub_ae : ∀ᵐ ω ∂P, ω ∈ B → ω ∈ {ω | M < -(X 1 ω)} := by
      filter_upwards [hStrict, hTendsto, hClaimsPos] with ω hStrictω hTendstoω hClaimsω hB
      have hArr_le : ∀ i < N, arrival i ω ≤ 1 / (N : ℝ) := fun i hi => by
        have hmem : Sum.inl i ∈ S := Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
        have := Set.mem_iInter₂.mp hB (Sum.inl i) hmem
        simpa [E] using this
      have hClm_gt : ∀ i < N, δ < claims i ω := fun i hi => by
        have hmem : Sum.inr i ∈ S := Finset.mem_union_right _ (Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
        have := Set.mem_iInter₂.mp hB (Sum.inr i) hmem
        simpa [E] using this
      have hT_le : ProbabilityTheory.arrival arrival (N - 1) ω ≤ 1 := by
        unfold ProbabilityTheory.arrival
        have hEqN : N - 1 + 1 = N := Nat.sub_add_cancel hN_pos
        rw [hEqN]
        calc ∑ i ∈ Finset.range N, arrival i ω
            ≤ ∑ _i ∈ Finset.range N, (1 / (N : ℝ)) :=
              Finset.sum_le_sum fun i hi => hArr_le i (Finset.mem_range.mp hi)
          _ = (N : ℝ) * (1 / (N : ℝ)) := by simp
          _ = 1 := by field_simp [hNR_pos.ne']
      have hJC_ge : N ≤ jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (1 : ℝ) := by
        have hlt : N - 1 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (1 : ℝ) :=
          (lt_jumpCount_iff hStrictω hTendstoω (N - 1) 1).mpr hT_le
        omega
      have hSum_gt : (N : ℝ) * δ <
          ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (1 : ℝ)),
            claims i ω := by
        have h1 : ∑ i ∈ Finset.range N, claims i ω ≤
            ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (1 : ℝ)),
              claims i ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJC_ge)
            (fun i _ _ => (hClaimsω i).le)
        have h2 : (N : ℝ) * δ < ∑ i ∈ Finset.range N, claims i ω := by
          have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hN_pos⟩
          have hlt := Finset.sum_lt_sum_of_nonempty hne (f := fun _ => δ) (g := fun i => claims i ω)
            (fun i hi => hClm_gt i (Finset.mem_range.mp hi))
          simpa using hlt
        linarith
      change M < -(X 1 ω)
      have hX1 : X 1 ω = (1 : ℝ) -
          ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (1 : ℝ)),
            claims i ω := by
        simp [X, riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
          ProbabilityTheory.piecewisePath]
      rw [hX1]
      linarith
    exact lt_of_lt_of_le hPB_pos (measure_mono_ae hSub_ae)
  -- Step 3: For every M : ℕ and T : ℕ, almost surely ∃ j : ℕ, M < -(X (T + j + 1) - X (T + j))
  have hFreq_ae : ∀ (M T : ℕ), ∀ᵐ ω ∂P,
      ∃ j : ℕ, (M : ℝ) < -(X (((T + j + 1 : ℕ) : ℝ≥0)) ω - X (((T + j : ℕ) : ℝ≥0)) ω) := by
    intro M T
    let A : ℕ → Set Ω := fun k =>
      {ω | (M : ℝ) < -(X (((k + 1 : ℕ) : ℝ≥0)) ω - X (((k : ℕ) : ℝ≥0)) ω)}
    have hA_meas : ∀ k, MeasurableSet (A k) := fun k =>
      measurableSet_lt measurable_const (hX_meas _ |>.sub (hX_meas _) |>.neg)
    set A0 : Set Ω := {ω | (M : ℝ) < -(X 1 ω)}
    have hA0_meas : MeasurableSet A0 := measurableSet_lt measurable_const (hX_meas 1).neg
    have hPA_eq : ∀ k : ℕ, P (A k) = P A0 := fun k => by
      have hst : ((k : ℕ) : ℝ≥0) ≤ ((k + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_succ k
      have hStat := (Kyprianou.Ch01.riskSurplus_increment_indep_stationary
        P arrival claims rate hrate F hd 1 ((k : ℕ) : ℝ≥0) ((k + 1 : ℕ) : ℝ≥0) hst).2
      have hsub : ((k + 1 : ℕ) : ℝ≥0) - ((k : ℕ) : ℝ≥0) = 1 := by
        ext; simp
      rw [hsub] at hStat
      have hpre1 : A k = (fun ω => X (((k + 1 : ℕ) : ℝ≥0)) ω - X (((k : ℕ) : ℝ≥0)) ω) ⁻¹' Set.Iio (-(M : ℝ)) := by
        ext ω
        simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
        constructor <;> intro h <;> linarith
      have hpre0 : A0 = X 1 ⁻¹' Set.Iio (-(M : ℝ)) := by
        ext ω
        simp only [A0, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
        constructor <;> intro h <;> linarith
      have hsub_meas : Measurable (fun ω => X (((k + 1 : ℕ) : ℝ≥0)) ω - X (((k : ℕ) : ℝ≥0)) ω) :=
        (hX_meas _).sub (hX_meas _)
      rw [hpre1, hpre0,
        ← Measure.map_apply hsub_meas measurableSet_Iio,
        ← Measure.map_apply (hX_meas 1) measurableSet_Iio]
      exact congrArg (fun μ => μ (Set.Iio (-(M : ℝ)))) hStat
    set p : ℝ := (P A0).toReal
    have hp_pos : 0 < p :=
      ENNReal.toReal_pos (ne_of_gt (hDrop_pos (M : ℝ))) (measure_ne_top P A0)
    have hp_le1 : p ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := P) (s := A0))
    have hPAc : ∀ k : ℕ, (P (A k)ᶜ).toReal = 1 - p := fun k => by
      rw [prob_compl_eq_one_sub (hA_meas k), hPA_eq k,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    let B : ℕ → Set Ω := fun m => ⋂ j ∈ Finset.range m, (A (T + j))ᶜ
    have hPB_pow : ∀ m : ℕ, (P (B m)).toReal = (1 - p) ^ m := by
      intro m
      induction m with
      | zero =>
          simp [B]
      | succ m ih =>
          have hBeq : B (m + 1) = B m ∩ (A (T + m))ᶜ := by
            ext ω
            simp only [B, Set.mem_iInter, Finset.mem_range, Set.mem_inter_iff]
            constructor
            · intro h
              exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h m (Nat.lt_succ_self m)⟩
            · rintro ⟨h1, h2⟩ j hj
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
              · exact h1 j hlt
              · exact h2
          have hst : (((T + m : ℕ) : ℝ≥0)) ≤ (((T + m + 1 : ℕ) : ℝ≥0)) := by
            exact_mod_cast Nat.le_succ (T + m)
          have hInd := (Kyprianou.Ch01.riskSurplus_increment_indep_stationary
            P arrival claims rate hrate F hd 1
            (((T + m : ℕ) : ℝ≥0)) (((T + m + 1 : ℕ) : ℝ≥0)) hst).1
          have hBm_meas : MeasurableSet[naturalSigma X (((T + m : ℕ) : ℝ≥0))] (B m) := by
            have hXle : ∀ r : ℕ, r ≤ T + m →
                @Measurable Ω ℝ (naturalSigma X (((T + m : ℕ) : ℝ≥0))) _ (X ((r : ℕ) : ℝ≥0)) := by
              intro r hr
              have hrle : ((r : ℕ) : ℝ≥0) ≤ (((T + m : ℕ) : ℝ≥0)) := by exact_mod_cast hr
              have hle_m : MeasurableSpace.comap (X ((r : ℕ) : ℝ≥0)) inferInstance ≤
                  naturalSigma X (((T + m : ℕ) : ℝ≥0)) :=
                le_iSup₂_of_le ((r : ℕ) : ℝ≥0) hrle le_rfl
              exact (comap_measurable (X ((r : ℕ) : ℝ≥0))).mono hle_m le_rfl
            refine @MeasurableSet.biInter _ _ (naturalSigma X (((T + m : ℕ) : ℝ≥0))) _ _
              (Finset.countable_toSet (Finset.range m)) fun j hj => ?_
            have hjlt : j < m := Finset.mem_range.mp hj
            have h1 := hXle (T + j + 1) (by omega)
            have h2 := hXle (T + j) (by omega)
            exact (@measurableSet_lt _ _ _ _ _ (naturalSigma X (((T + m : ℕ) : ℝ≥0))) _ _ _ _ _
              measurable_const (h1.sub h2).neg).compl
          have hStep_meas : MeasurableSet[MeasurableSpace.comap
              (fun ω => X (((T + m + 1 : ℕ) : ℝ≥0)) ω - X (((T + m : ℕ) : ℝ≥0)) ω) inferInstance]
              (A (T + m))ᶜ := by
            refine ⟨(Set.Iio (-(M : ℝ)))ᶜ, measurableSet_Iio.compl, ?_⟩
            ext ω
            simp only [A, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Iio, Set.mem_setOf_eq, not_lt]
            constructor <;> intro h <;> linarith
          have hMul : P (B m ∩ (A (T + m))ᶜ) = P (B m) * P (A (T + m))ᶜ :=
            (Indep_iff _ _ P).mp hInd.symm (B m) (A (T + m))ᶜ hBm_meas hStep_meas
          rw [hBeq, hMul, ENNReal.toReal_mul, ih, hPAc (T + m), pow_succ]
    set C : Set Ω := ⋂ j : ℕ, (A (T + j))ᶜ
    have hPC_zero : P C = 0 := by
      have htoReal : (P C).toReal = 0 := by
        apply le_antisymm _ ENNReal.toReal_nonneg
        have htend : Tendsto (fun m : ℕ => (1 - p) ^ m) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
        refine ge_of_tendsto htend ?_
        filter_upwards with m
        have hsub : C ⊆ B m := fun ω hω =>
          Set.mem_iInter₂.mpr fun j _ => Set.mem_iInter.mp hω j
        rw [← hPB_pow m]
        exact ENNReal.toReal_mono (measure_ne_top P (B m)) (measure_mono hsub)
      exact (ENNReal.toReal_eq_zero_iff (P C)).mp htoReal |>.resolve_right (measure_ne_top P C)
    rw [ae_iff]
    convert hPC_zero using 2
    ext ω
    simp [C, A]
  -- Step 4: Countable intersection over M, T : ℕ and lower bound W_t ≥ X_s - X_t
  have hAll_ae : ∀ᵐ ω ∂P,
      (∀ n : ℕ, 0 < claims n ω) ∧
      ∀ (M T : ℕ), ∃ j : ℕ,
        (M : ℝ) < -(X (((T + j + 1 : ℕ) : ℝ≥0)) ω - X (((T + j : ℕ) : ℝ≥0)) ω) := by
    refine hClaimsPos.and ?_
    rw [ae_all_iff]
    intro M
    rw [ae_all_iff]
    intro T
    exact hFreq_ae M T
  have hTarget_ae : ∀ᵐ ω ∂P, ∀ M : ℝ, ∀ T : ℝ≥0,
      ∃ t : ℝ≥0, T ≤ t ∧ M < queueWorkload arrival claims w t ω := by
    filter_upwards [hAll_ae] with ω ⟨hClmω, hFreqω⟩ M T
    obtain ⟨m, hm⟩ := exists_nat_gt M
    obtain ⟨TN, hTN⟩ := exists_nat_ge (T : ℝ)
    obtain ⟨j, hj⟩ := hFreqω m TN
    set s : ℝ≥0 := ((TN + j : ℕ) : ℝ≥0)
    set t : ℝ≥0 := ((TN + j + 1 : ℕ) : ℝ≥0)
    have hT_le_t : T ≤ t := by
      rw [← NNReal.coe_le_coe]
      have h1 : (T : ℝ) ≤ (TN : ℝ) := hTN
      have h2 : (TN : ℝ) ≤ ((TN + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : TN ≤ TN + j + 1)
      simpa [t] using h1.trans h2
    have hs_le_t : s ≤ t := by dsimp [s, t]; exact_mod_cast Nat.le_succ (TN + j)
    have hBdd : BddAbove {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω} := by
      refine ⟨(t : ℝ), ?_⟩
      rintro z ⟨u, hu, rfl⟩
      have hAgg_nonneg : 0 ≤ aggregateClaims arrival claims u ω := by
        simp only [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]
        have hsum : 0 ≤ ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (u : ℝ)),
            claims i ω := Finset.sum_nonneg fun i _ => (hClmω i).le
        linarith
      have hXu : X u ω = (u : ℝ) - aggregateClaims arrival claims u ω := by
        simp [X, riskSurplus]
      have huR : (u : ℝ) ≤ (t : ℝ) := hu
      linarith
    have hXs_le_sup : X s ω ≤ sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω} :=
      le_csSup hBdd ⟨s, hs_le_t, rfl⟩
    have hW_ge : X s ω - X t ω ≤ queueWorkload arrival claims w t ω := by
      dsimp [queueWorkload]
      have hle : X s ω ≤ max w (sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω}) :=
        hXs_le_sup.trans (le_max_right _ _)
      linarith
    refine ⟨t, hT_le_t, ?_⟩
    linarith
  set Target : Set Ω := {ω | ∀ M : ℝ, ∀ T : ℝ≥0,
      ∃ t : ℝ≥0, T ≤ t ∧ M < queueWorkload arrival claims w t ω}
  have hCompl : P Targetᶜ = 0 := ae_iff.mp hTarget_ae
  have hP1 : P Target = 1 := by
    apply le_antisymm prob_le_one
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P (Target ∪ Targetᶜ) := by rw [Set.union_compl_self]
      _ ≤ P Target + P Targetᶜ := measure_union_le _ _
      _ = P Target := by rw [hCompl, add_zero]
  rw [hP1, ENNReal.toReal_one]
