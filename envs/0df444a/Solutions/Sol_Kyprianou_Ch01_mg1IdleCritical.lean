-- Prove2me | solution 1 for Kyprianou.Ch01.mg1IdleCritical
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T16:07:30.231203+00:00
-- url     : https://prove2.me/submissions/36fb9c4b-8852-48d8-ab34-e48a6439f826

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_mg1IdleRegulatorIdentity
import Theorems.Thm_Kyprianou_Ch01_queueUpperPassageProbability
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootIff
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
universe u

private lemma expMeasure_map_mul {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (expMeasure r).map (fun x => c * x) = expMeasure (r / c) := by
  have hrc : 0 < r / c := div_pos hr hc
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have : IsProbabilityMeasure (expMeasure (r / c)) := isProbabilityMeasure_expMeasure hrc
  have : IsProbabilityMeasure ((expMeasure r).map (fun x => c * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul c).aemeasurable
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply (measurable_const_mul c) measurableSet_Iic]
  have hpre : (fun x : ℝ => c * x) ⁻¹' Set.Iic a = Set.Iic (a / c) := by
    ext x
    simp [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hc, mul_comm]
  rw [hpre]
  have h1 : ((expMeasure r) (Set.Iic (a / c))).toReal = cdf (expMeasure r) (a / c) := by
    rw [cdf_eq_real, Measure.real]
  have h2 : ((expMeasure (r / c)) (Set.Iic a)).toReal = cdf (expMeasure (r / c)) a := by
    rw [cdf_eq_real, Measure.real]
  have hcdf : cdf (expMeasure r) (a / c) = cdf (expMeasure (r / c)) a := by
    rw [cdf_expMeasure_eq hr, cdf_expMeasure_eq hrc]
    have hiff : (0 ≤ a / c) ↔ (0 ≤ a) := by rw [le_div_iff₀ hc, zero_mul]
    by_cases ha : 0 ≤ a
    · rw [if_pos (hiff.mpr ha), if_pos ha]
      congr 2
      field_simp [hc.ne']
    · rw [if_neg (mt hiff.mp ha), if_neg ha]
  have htoReal : ((expMeasure r) (Set.Iic (a / c))).toReal = ((expMeasure (r / c)) (Set.Iic a)).toReal := by
    rw [h1, h2, hcdf]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp htoReal

private lemma scaled_driver
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (c : ℝ≥0) (hc : 0 < c) :
    IsCompoundPoissonDriver (fun n ω => (c : ℝ) * arrival n ω) claims (rate / c) F P := by
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  have hcR : (0 : ℝ) < (c : ℝ) := NNReal.coe_pos.mpr hc
  refine
    { measurable_interarrival := fun n => measurable_const.mul (hd.measurable_interarrival n)
      measurable_mark := hd.measurable_mark
      indep := ?_
      law_interarrival := fun n => ?_
      law_mark := hd.law_mark }
  · let g : ℕ ⊕ ℕ → ℝ → ℝ := Sum.elim (fun _ x => (c : ℝ) * x) (fun _ x => x)
    have hg : ∀ i, Measurable (g i) := fun i => by
      cases i with
      | inl _ => exact measurable_const_mul (c : ℝ)
      | inr _ => exact measurable_id
    have hcomp := hd.indep.comp g hg
    convert hcomp using 1
    ext i ω
    cases i <;> rfl
  · refine ⟨(measurable_const.mul (hd.measurable_interarrival n)).aemeasurable, ?_⟩
    have hcomp : (fun ω => (c : ℝ) * arrival n ω) = (fun x => (c : ℝ) * x) ∘ arrival n := rfl
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
      (measurable_const_mul (c : ℝ)).aemeasurable (hd.measurable_interarrival n).aemeasurable,
      (hd.law_interarrival n).map_eq, expMeasure_map_mul hrateR hcR]
    simp

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
    (hcritical : (rate : ℝ) * mu = 1) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1 := by
  intro w hw
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
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
    ext ω; simp [not_lt]
  have hReg := Kyprianou.Ch01.mg1IdleRegulatorIdentity P arrival claims rate hrate F hd hclaimpos w hw
  -- Key: for every y > 0, P(∃ t > 0, y < X_t) = 1 via overloaded time-scaling coupling
  have hPass_one : ∀ y : ℝ, 0 < y →
      P {ω | ∃ t : ℝ≥0, 0 < t ∧ y < riskSurplus arrival claims 1 0 t ω} = 1 := by
    intro y hy
    set A : Set Ω := {ω | ∃ t : ℝ≥0, 0 < t ∧ y < riskSurplus arrival claims 1 0 t ω}
    have hge_exp : ∀ ε : ℝ, 0 < ε → Real.exp (-ε * y) ≤ (P A).toReal := by
      intro ε hε
      -- 1. Show queueLaplaceExponent rate F ε > 0
      have hF_pos : ∀ᵐ z ∂F, 0 < z := by
        rw [ae_iff]
        convert hclaimpos using 2
        ext z; simp [not_lt]
      have hExp_int : Integrable (fun z : ℝ => 1 - Real.exp (-ε * z)) F := by
        refine (integrable_const (1 : ℝ)).mono' ?_ ?_
        · exact (measurable_const.sub (Real.continuous_exp.measurable.comp
            (measurable_const.mul measurable_id))).aestronglyMeasurable
        · filter_upwards [hF_pos] with z hz
          have h1 : Real.exp (-ε * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          have h0 : 0 < Real.exp (-ε * z) := Real.exp_pos _
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith
      have hDiff_int : Integrable (fun z : ℝ => ε * z - (1 - Real.exp (-ε * z))) F :=
        (hclaimint.const_mul ε).sub hExp_int
      have hDiff_pos_ae : ∀ᵐ z ∂F, 0 < ε * z - (1 - Real.exp (-ε * z)) := by
        filter_upwards [hF_pos] with z hz
        have hne : -ε * z ≠ 0 := by nlinarith
        have hlt := Real.add_one_lt_exp hne
        linarith
      have hDiff_int_pos : 0 < ∫ z : ℝ, (ε * z - (1 - Real.exp (-ε * z))) ∂F := by
        have hpos_iff := integral_pos_iff_support_of_nonneg_ae
          (hDiff_pos_ae.mono fun z hz => hz.le) hDiff_int
        rw [hpos_iff]
        have hSupp : F (Function.support (fun z : ℝ => ε * z - (1 - Real.exp (-ε * z)))) = 1 := by
          have hAE_mem : ∀ᵐ z ∂F, z ∈ Function.support (fun z : ℝ => ε * z - (1 - Real.exp (-ε * z))) :=
            hDiff_pos_ae.mono fun z hz => ne_of_gt hz
          have hCompl : F (Function.support (fun z : ℝ => ε * z - (1 - Real.exp (-ε * z))))ᶜ = 0 :=
            ae_iff.mp hAE_mem
          apply le_antisymm prob_le_one
          calc (1 : ℝ≥0∞) = F Set.univ := measure_univ.symm
            _ = F (Function.support _ ∪ (Function.support _)ᶜ) := by rw [Set.union_compl_self]
            _ ≤ F (Function.support _) + F (Function.support _)ᶜ := measure_union_le _ _
            _ = F (Function.support _) := by rw [hCompl, add_zero]
        rw [hSupp]
        exact zero_lt_one
      set I : ℝ := ∫ z : ℝ, (1 - Real.exp (-ε * z)) ∂F
      have hI_nonneg : 0 ≤ I := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [hF_pos] with z hz
        change 0 ≤ 1 - Real.exp (-ε * z)
        have h1 : Real.exp (-ε * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      have hLap_pos : 0 < queueLaplaceExponent rate F ε := by
        have h1 : (∫ z : ℝ, (ε * z - (1 - Real.exp (-ε * z))) ∂F) = ε * mu - I := by
          rw [integral_sub (hclaimint.const_mul ε) hExp_int, integral_const_mul, hmean]
        have h2 : 0 < ε * mu - I := by rwa [h1] at hDiff_int_pos
        dsimp [queueLaplaceExponent]
        have h3 : 0 < (rate : ℝ) * (ε * mu - I) := mul_pos hrateR h2
        have h4 : (rate : ℝ) * (ε * mu - I) = ε - (rate : ℝ) * I := by
          calc (rate : ℝ) * (ε * mu - I) = ε * ((rate : ℝ) * mu) - (rate : ℝ) * I := by ring
            _ = ε - (rate : ℝ) * I := by rw [hcritical, mul_one]
        linarith
      -- 2. Choose scaling factor c ∈ (0, 1) so that queueLaplaceExponent (rate / c) F ε > 0
      have hrI_lt : (rate : ℝ) * I < ε := by
        dsimp [queueLaplaceExponent] at hLap_pos; linarith
      set cR : ℝ := ((rate : ℝ) * I + ε) / (2 * ε)
      have hcR_pos : 0 < cR := by
        have : 0 ≤ (rate : ℝ) * I := mul_nonneg hrateR.le hI_nonneg
        positivity
      have hcR_lt1 : cR < 1 := by
        dsimp [cR]
        rw [div_lt_one (by positivity)]
        linarith
      set c : ℝ≥0 := ⟨cR, hcR_pos.le⟩
      have hc_pos : 0 < c := NNReal.coe_pos.mp hcR_pos
      set rate' : ℝ≥0 := rate / c
      have hrate'_pos : 0 < rate' := div_pos hrate hc_pos
      have hrate'_coe : (rate' : ℝ) = (rate : ℝ) / cR := rfl
      have hOverload' : 1 < (rate' : ℝ) * mu := by
        rw [hrate'_coe, div_mul_eq_mul_div, hcritical, one_lt_div hcR_pos]
        exact hcR_lt1
      have hLap'_pos : 0 < queueLaplaceExponent rate' F ε := by
        dsimp [queueLaplaceExponent]
        rw [hrate'_coe, div_mul_eq_mul_div]
        have hlt : (rate : ℝ) * I < cR * ε := by
          dsimp [cR]
          have : ((rate : ℝ) * I + ε) / (2 * ε) * ε = ((rate : ℝ) * I + ε) / 2 := by
            field_simp [hε.ne']
          rw [this]
          linarith
        have hdiv : (rate : ℝ) * I / cR < ε := (div_lt_iff₀ hcR_pos).mpr (by linarith)
        linarith
      -- 3. Positive root theta_c of rate' satisfies 0 < theta_c < ε
      obtain ⟨theta, htheta_pos, htheta_root⟩ :=
        (Kyprianou.Ch01.queueLaplaceExponent_rootIff rate' hrate'_pos F hclaimpos
          hclaimint mu hmu hmean).mpr hOverload'
      have htheta_lt : theta < ε := by
        by_contra hge
        have hle : ε ≤ theta := le_of_not_gt hge
        rcases eq_or_lt_of_le hle with rfl | hlt
        · linarith
        · have hConv := Kyprianou.Ch01.queueLaplaceExponent_strictConvex rate' hrate'_pos F
            hclaimpos hclaimint mu hmu hmean
          have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
          have ht_mem : theta ∈ Set.Ici (0 : ℝ) := htheta_pos.le
          have hne : (0 : ℝ) ≠ theta := htheta_pos.ne
          set a : ℝ := 1 - ε / theta
          set b : ℝ := ε / theta
          have ha_pos : 0 < a := by
            dsimp [a]; rw [sub_pos, div_lt_one htheta_pos]; exact hlt
          have hb_pos : 0 < b := div_pos hε htheta_pos
          have hab : a + b = 1 := by dsimp [a, b]; ring
          have hcomb : a • (0 : ℝ) + b • theta = ε := by
            dsimp [a, b]; simp only [mul_zero, zero_add]
            field_simp [htheta_pos.ne']
          have hStrictIneq := hConv.2 h0_mem ht_mem hne ha_pos hb_pos hab
          rw [hcomb, Kyprianou.Ch01.queueLaplaceExponent_zero, htheta_root] at hStrictIneq
          simp only [smul_eq_mul, mul_zero, add_zero] at hStrictIneq
          linarith
      -- 4. Apply queueUpperPassageProbability to scaled driver and dominate pathwise
      let arrival' : ℕ → Ω → ℝ := fun n ω => cR * arrival n ω
      have hd' : IsCompoundPoissonDriver arrival' claims rate' F P :=
        scaled_driver P arrival claims rate hrate F hd c hc_pos
      set A' : Set Ω := {ω | ∃ s : ℝ≥0, 0 < s ∧ y < riskSurplus arrival' claims 1 0 s ω}
      have hP_A' : (P A').toReal = Real.exp (-theta * y) :=
        Kyprianou.Ch01.queueUpperPassageProbability P arrival' claims rate' hrate'_pos F hd'
          hclaimpos hclaimint mu hmean hOverload' theta htheta_pos htheta_root y hy
      have hSub_ae : ∀ᵐ ω ∂P, ω ∈ A' → ω ∈ A := by
        filter_upwards [hPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω hmem
        obtain ⟨s, hs_pos, hsy⟩ := hmem
        set t : ℝ≥0 := s / c
        have ht_pos : 0 < t := div_pos hs_pos hc_pos
        have hT_eq : ∀ n, ProbabilityTheory.arrival arrival' n ω =
            cR * ProbabilityTheory.arrival arrival n ω := fun n => by
          dsimp [arrival', ProbabilityTheory.arrival]
          rw [Finset.mul_sum]
        have hStrict' : StrictMono (fun n => ProbabilityTheory.arrival arrival' n ω) := fun i j hij => by
          dsimp only
          rw [hT_eq i, hT_eq j]
          exact mul_lt_mul_of_pos_left (hStrictω hij) hcR_pos
        have hTendsto' : Tendsto (fun n => ProbabilityTheory.arrival arrival' n ω) atTop atTop := by
          have : (fun n => ProbabilityTheory.arrival arrival' n ω) =
              fun n => cR * ProbabilityTheory.arrival arrival n ω := funext hT_eq
          rw [this]
          exact Tendsto.const_mul_atTop hcR_pos hTendstoω
        have hJC_eq : jumpCount (fun n => ProbabilityTheory.arrival arrival' n ω) (s : ℝ) =
            jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) := by
          apply le_antisymm
          · by_contra hgt
            have hlt := lt_of_not_ge hgt
            set n := jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)
            have h1 : ProbabilityTheory.arrival arrival' n ω ≤ (s : ℝ) :=
              (lt_jumpCount_iff hStrict' hTendsto' n (s : ℝ)).mp hlt
            rw [hT_eq n] at h1
            have h2 : ProbabilityTheory.arrival arrival n ω ≤ (t : ℝ) := by
              have htcoe : (t : ℝ) = (s : ℝ) / cR := rfl
              rw [htcoe, le_div_iff₀ hcR_pos, mul_comm]
              exact h1
            have h3 : n < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) :=
              (lt_jumpCount_iff hStrictω hTendstoω n (t : ℝ)).mpr h2
            exact lt_irrefl _ h3
          · by_contra hgt
            have hlt := lt_of_not_ge hgt
            set n := jumpCount (fun n => ProbabilityTheory.arrival arrival' n ω) (s : ℝ)
            have h1 : ProbabilityTheory.arrival arrival n ω ≤ (t : ℝ) :=
              (lt_jumpCount_iff hStrictω hTendstoω n (t : ℝ)).mp hlt
            have h2 : ProbabilityTheory.arrival arrival' n ω ≤ (s : ℝ) := by
              rw [hT_eq n]
              have htcoe : (t : ℝ) = (s : ℝ) / cR := rfl
              rw [htcoe, le_div_iff₀ hcR_pos, mul_comm] at h1
              exact h1
            have h3 : n < jumpCount (fun n => ProbabilityTheory.arrival arrival' n ω) (s : ℝ) :=
              (lt_jumpCount_iff hStrict' hTendsto' n (s : ℝ)).mpr h2
            exact lt_irrefl _ h3
        have hs_le_t : (s : ℝ) ≤ (t : ℝ) := by
          have htcoe : (t : ℝ) = (s : ℝ) / cR := rfl
          rw [htcoe, le_div_iff₀ hcR_pos]
          nlinarith [s.2]
        have hSurp_le : riskSurplus arrival' claims 1 0 s ω ≤ riskSurplus arrival claims 1 0 t ω := by
          simp only [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
            ProbabilityTheory.piecewisePath, hJC_eq]
          linarith
        exact ⟨t, ht_pos, lt_of_lt_of_le hsy hSurp_le⟩
      have hP_le : P A' ≤ P A := measure_mono_ae hSub_ae
      have hP_toReal_le : (P A').toReal ≤ (P A).toReal :=
        ENNReal.toReal_mono (measure_ne_top P A) hP_le
      have hexp_le : Real.exp (-ε * y) ≤ Real.exp (-theta * y) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith [hP_A']
    have htoReal_eq1 : (P A).toReal = 1 := by
      apply le_antisymm
      · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := P) (s := A))
      · refine le_of_forall_pos_le_add fun δ hδ => ?_
        have h1 : Tendsto (fun ε : ℝ => Real.exp (-ε * y)) (𝓝 0) (𝓝 (Real.exp (-0 * y))) :=
          (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousAt.tendsto
        rw [neg_zero, zero_mul, Real.exp_zero] at h1
        have hEv := h1.eventually (lt_mem_nhds (by linarith : 1 - δ < 1))
        rw [Metric.eventually_nhds_iff] at hEv
        obtain ⟨r, hr_pos, hr⟩ := hEv
        have hε_pos : 0 < r / 2 := by positivity
        have hdist : dist (r / 2) 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; linarith
        have hexp_gt : 1 - δ < Real.exp (-(r / 2) * y) := hr hdist
        linarith [hge_exp (r / 2) hε_pos]
    exact (ENNReal.toReal_eq_one_iff (P A)).mp htoReal_eq1
  -- Helper: measurable rational approximation for A y = {∃ t > 0, y < X_t}
  have hMeas_surp : ∀ t : ℝ≥0, Measurable (riskSurplus arrival claims 1 0 t) := by
    intro t
    have hArrSum : ∀ n, Measurable (fun ω => ProbabilityTheory.arrival arrival n ω) := fun n =>
      Finset.measurable_sum (Finset.range (n + 1)) (fun i _ => hd.measurable_interarrival i)
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
          ((Finset.measurable_sum (Finset.range k) fun i _ => hd.measurable_mark i) hs)
    have hEq : riskSurplus arrival claims 1 0 t =
        fun ω => 0 + 1 * (t : ℝ) - (0 + 0 * (t : ℝ) +
          ∑ i ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ)),
            claims i ω) := by
      ext ω
      simp [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath]
    rw [hEq]
    exact measurable_const.sub (measurable_const.add hSumClm)
  -- Intersect over all n : ℕ (y = w + n + 1) and conclude totalIdleTime = ⊤ a.s.
  have hAll_pass : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∃ t : ℝ≥0, 0 < t ∧ w + (n : ℝ) + 1 < riskSurplus arrival claims 1 0 t ω := by
    rw [ae_all_iff]
    intro n
    set y : ℝ := w + (n : ℝ) + 1
    have hy_pos : 0 < y := by positivity
    set A : Set Ω := {ω | ∃ t : ℝ≥0, 0 < t ∧ y < riskSurplus arrival claims 1 0 t ω}
    set Arat : Set Ω := ⋃ q : {q : ℚ // (0 : ℚ) < q},
      {ω | y < riskSurplus arrival claims 1 0 ⟨(q.1 : ℝ), by exact_mod_cast q.2.le⟩ ω}
    have hArat_meas : MeasurableSet Arat :=
      MeasurableSet.iUnion fun q => measurableSet_lt measurable_const (hMeas_surp _)
    have hA_eq_Arat : A =ᵐ[P] Arat := by
      filter_upwards [hPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
      change (ω ∈ A) = (ω ∈ Arat)
      apply propext
      constructor
      · rintro ⟨t, ht_pos, hyt⟩
        set T := fun n => ProbabilityTheory.arrival arrival n ω
        set k := jumpCount T (t : ℝ)
        have hlt_next : (t : ℝ) < T k := by
          have hnot : ¬ (k < jumpCount T (t : ℝ)) := lt_irrefl _
          rw [lt_jumpCount_iff hStrictω hTendstoω] at hnot
          exact lt_of_not_ge hnot
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt_next
        have hq_pos : (0 : ℚ) < q := by
          have : (0 : ℝ) < (q : ℝ) := lt_trans (NNReal.coe_pos.mpr ht_pos) hq1
          exact_mod_cast this
        rw [Set.mem_iUnion]
        refine ⟨⟨q, hq_pos⟩, ?_⟩
        have hjq : jumpCount T (q : ℝ) = k := by
          have hle_k : ¬ (k < jumpCount T (q : ℝ)) := by
            rw [lt_jumpCount_iff hStrictω hTendstoω]; exact not_le.mpr hq2
          cases hk : k with
          | zero => omega
          | succ i =>
              have hi_lt : i < jumpCount T (t : ℝ) := by omega
              have hTi_le : T i ≤ (t : ℝ) := (lt_jumpCount_iff hStrictω hTendstoω i (t : ℝ)).mp hi_lt
              have hi_lt' : i < jumpCount T (q : ℝ) :=
                (lt_jumpCount_iff hStrictω hTendstoω i (q : ℝ)).mpr (le_trans hTi_le hq1.le)
              omega
        have hq_val : riskSurplus arrival claims 1 0 ⟨(q : ℝ), by exact_mod_cast hq_pos.le⟩ ω =
            riskSurplus arrival claims 1 0 t ω + ((q : ℝ) - (t : ℝ)) := by
          unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson
            ProbabilityTheory.piecewisePath
          change 0 + 1 * (q : ℝ) - (0 + 0 * (q : ℝ) + ∑ i ∈ Finset.range (jumpCount T (q : ℝ)), claims i ω) =
            0 + 1 * (t : ℝ) - (0 + 0 * (t : ℝ) + ∑ i ∈ Finset.range k, claims i ω) + ((q : ℝ) - (t : ℝ))
          rw [hjq]; ring
        change y < riskSurplus arrival claims 1 0 ⟨(q : ℝ), by exact_mod_cast hq_pos.le⟩ ω
        rw [hq_val]; linarith
      · intro h
        rw [Set.mem_iUnion] at h
        obtain ⟨⟨q, hq_pos⟩, hmem⟩ := h
        have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
        exact ⟨⟨(q : ℝ), hqR_pos.le⟩, NNReal.coe_pos.mp hqR_pos, hmem⟩
    have hP1 : P Arat = 1 := by
      rw [← measure_congr hA_eq_Arat]
      exact hPass_one y hy_pos
    have hArat_ae : ∀ᵐ ω ∂P, ω ∈ Arat := by
      rw [ae_iff]
      have hcompl : P Aratᶜ = 0 := by
        rw [prob_compl_eq_one_sub hArat_meas, hP1, tsub_self]
      exact hcompl
    filter_upwards [hArat_ae, hA_eq_Arat] with ω hmem hEq
    exact (eq_iff_iff.mp hEq).mpr hmem
  have hAE_top : ∀ᵐ ω ∂P, totalIdleTime arrival claims w ω = ⊤ := by
    filter_upwards [hReg, hClaimsPos, hAll_pass] with ω hRegω hClaimsω hPassω
    rw [eq_top_iff]
    refine le_of_forall_lt fun b hb => ?_
    have hb_ne : b ≠ ⊤ := hb.ne
    obtain ⟨n, hn⟩ := exists_nat_gt b.toReal
    obtain ⟨t, _, hxt⟩ := hPassω n
    have hb_lt : b < ENNReal.ofReal ((n : ℝ) + 1) := by
      rw [← ENNReal.ofReal_toReal hb_ne]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
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
    have hM_le_int : (n : ℝ) + 1 ≤ ∫ s in (0 : ℝ)..(t : ℝ),
        (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
          then (1 : ℝ) else 0) ∂volume := by
      rw [hRegω t]
      refine le_trans ?_ (le_max_left _ _)
      linarith
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
    apply le_antisymm prob_le_one
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P ({ω | totalIdleTime arrival claims w ω = ⊤} ∪
            {ω | totalIdleTime arrival claims w ω = ⊤}ᶜ) := by rw [Set.union_compl_self]
      _ ≤ P {ω | totalIdleTime arrival claims w ω = ⊤} +
            P ({ω | totalIdleTime arrival claims w ω = ⊤}ᶜ) := measure_union_le _ _
      _ = P {ω | totalIdleTime arrival claims w ω = ⊤} := by rw [hCompl, add_zero]
  rw [hProb]
  simp
