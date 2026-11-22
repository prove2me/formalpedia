-- Prove2me | solution 1 for Kyprianou.Ch01.mg1IdleRegulatorIdentity
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:32:09.364945+00:00
-- url     : https://prove2.me/submissions/d14a4de2-21d0-4cb7-91ca-755cebf87651

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

private def brk (T : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => T k

private lemma brk_nonneg {T : ℕ → ℝ} (hT0 : 0 < T 0) (hStrict : StrictMono T) :
    ∀ k : ℕ, 0 ≤ brk T k
  | 0 => le_rfl
  | k + 1 => by
      dsimp [brk]
      exact le_trans hT0.le (hStrict.monotone (Nat.zero_le k))

private lemma brk_le_succ {T : ℕ → ℝ} (hT0 : 0 < T 0) (hStrict : StrictMono T) :
    ∀ k : ℕ, brk T k ≤ brk T (k + 1)
  | 0 => hT0.le
  | k + 1 => (hStrict (Nat.lt_succ_self k)).le

private lemma jumpCount_eq_of_brk {T : ℕ → ℝ}
    (hStrict : StrictMono T) (hTendsto : Tendsto T atTop atTop)
    {k : ℕ} {u : ℝ} (h1 : brk T k ≤ u) (h2 : u < brk T (k + 1)) :
    jumpCount T u = k := by
  cases k with
  | zero =>
      dsimp [brk] at h2
      have hnot : ¬ (0 < jumpCount T u) := by
        rw [lt_jumpCount_iff hStrict hTendsto]
        exact not_le.mpr h2
      omega
  | succ j =>
      dsimp [brk] at h1 h2
      have hgt : j < jumpCount T u := (lt_jumpCount_iff hStrict hTendsto j u).mpr h1
      have hle : ¬ (j + 1 < jumpCount T u) := by
        rw [lt_jumpCount_iff hStrict hTendsto]
        exact not_le.mpr h2
      omega

private lemma brk_le_self_lt_succ {T : ℕ → ℝ}
    (hStrict : StrictMono T) (hTendsto : Tendsto T atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    brk T (jumpCount T t) ≤ t ∧ t < brk T (jumpCount T t + 1) := by
  set N := jumpCount T t with hN
  constructor
  · cases hN' : N with
    | zero => simpa [brk] using ht
    | succ j =>
        dsimp [brk]
        have hj : j < jumpCount T t := by omega
        exact (lt_jumpCount_iff hStrict hTendsto j t).mp hj
  · dsimp [brk]
    have hnot : ¬ (N < jumpCount T t) := by omega
    rw [lt_jumpCount_iff hStrict hTendsto] at hnot
    exact lt_of_not_ge hnot

private lemma regulator_deterministic
    (T Y : ℕ → ℝ) (hT0 : 0 < T 0) (hStrict : StrictMono T)
    (hTendsto : Tendsto T atTop atTop) (hY : ∀ n, 0 ≤ Y n)
    (w : ℝ) (hw : 0 ≤ w) :
    let S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, Y i
    let X : ℝ → ℝ := fun u => u - S (jumpCount T u)
    let M0 : ℝ → ℝ := fun t => sSup {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)}
    let M : ℝ → ℝ := fun t => max w (M0 t)
    let ind : ℝ → ℝ := fun u =>
      if M (Real.toNNReal u : ℝ) - X (Real.toNNReal u : ℝ) = 0 then (1 : ℝ) else 0
    ∀ t : ℝ≥0,
      (∫ s in (0 : ℝ)..(t : ℝ), ind s ∂volume) = max (M0 (t : ℝ) - w) 0 := by
  intro S X M0 M ind
  have hS_nonneg : ∀ k, 0 ≤ S k := fun k =>
    Finset.sum_nonneg (fun i _ => hY i)
  have hS_mono : ∀ {j k}, j ≤ k → S j ≤ S k := fun hjk =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) (fun i _ _ => hY i)
  have hX_le : ∀ u : ℝ, X u ≤ u := fun u => by
    dsimp [X]
    linarith [hS_nonneg (jumpCount T u)]
  have hX_zero : X 0 = 0 := by
    have hj0 : jumpCount T 0 = 0 := jumpCount_eq_of_brk hStrict hTendsto (k := 0) le_rfl hT0
    simp [X, S, hj0]
  have hBdd : ∀ t : ℝ, BddAbove {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)} := by
    intro t
    refine ⟨t, ?_⟩
    rintro x ⟨s, hs, rfl⟩
    exact le_trans (hX_le (s : ℝ)) hs
  have hNonempty : ∀ {t : ℝ}, 0 ≤ t →
      {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)}.Nonempty := by
    intro t ht
    exact ⟨X 0, ⟨0, ht, rfl⟩⟩
  have hM0_ge : ∀ {t : ℝ} {s : ℝ≥0}, (s : ℝ) ≤ t → X (s : ℝ) ≤ M0 t := by
    intro t s hs
    exact le_csSup (hBdd t) ⟨s, hs, rfl⟩
  have hM0_mono : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ → M0 t₁ ≤ M0 t₂ := by
    intro t₁ t₂ ht₁ hle
    refine csSup_le_csSup (hBdd t₂) (hNonempty ht₁) ?_
    rintro x ⟨s, hs, rfl⟩
    exact ⟨s, le_trans hs hle, rfl⟩
  have hM0_zero : M0 0 = 0 := by
    apply le_antisymm
    · refine csSup_le (hNonempty le_rfl) ?_
      rintro x ⟨s, hs, rfl⟩
      have hs0 : (s : ℝ) = 0 := le_antisymm hs s.2
      rw [hs0, hX_zero]
    · have h0 := hM0_ge (t := 0) (s := 0) le_rfl
      simpa [hX_zero] using h0
  have hM_zero : M 0 = w := by
    dsimp [M]
    rw [hM0_zero]
    exact max_eq_left hw
  have hM0_step : ∀ (k : ℕ) (c : ℝ),
      brk T k ≤ c → c ≤ brk T (k + 1) →
      M0 c = max (M0 (brk T k)) (c - S k) := by
    intro k c hc1 hc2
    have hbk_nonneg : 0 ≤ brk T k := brk_nonneg hT0 hStrict k
    have hc_nonneg : 0 ≤ c := le_trans hbk_nonneg hc1
    apply le_antisymm
    · refine csSup_le (hNonempty hc_nonneg) ?_
      rintro x ⟨s, hs, rfl⟩
      by_cases hsb : (s : ℝ) ≤ brk T k
      · exact le_trans (hM0_ge hsb) (le_max_left _ _)
      · push_neg at hsb
        by_cases hslt : (s : ℝ) < brk T (k + 1)
        · have hj : jumpCount T (s : ℝ) = k :=
            jumpCount_eq_of_brk hStrict hTendsto hsb.le hslt
          have hXs : X (s : ℝ) = (s : ℝ) - S k := by simp [X, hj]
          rw [hXs]
          exact le_trans (by linarith) (le_max_right _ _)
        · push_neg at hslt
          have hseq : (s : ℝ) = brk T (k + 1) := le_antisymm (le_trans hs hc2) hslt
          have hceq : c = brk T (k + 1) := le_antisymm hc2 (le_trans hslt hs)
          have hj_ge : k ≤ jumpCount T (s : ℝ) := by
            cases k with
            | zero => exact Nat.zero_le _
            | succ j =>
                have : j < jumpCount T (s : ℝ) := by
                  rw [lt_jumpCount_iff hStrict hTendsto]
                  dsimp [brk] at hsb
                  exact hsb.le
                omega
          have hXs_le : X (s : ℝ) ≤ c - S k := by
            dsimp [X]
            have := hS_mono hj_ge
            linarith
          exact le_trans hXs_le (le_max_right _ _)
    · apply max_le
      · exact hM0_mono hbk_nonneg hc1
      · by_cases heq : c = brk T k
        · rw [heq]
          have hX_bk : X (brk T k) = brk T k - S k := by
            have hlt : brk T k < brk T (k + 1) := by
              cases k with
              | zero => exact hT0
              | succ j => exact hStrict (Nat.lt_succ_self j)
            have hj := jumpCount_eq_of_brk hStrict hTendsto le_rfl hlt
            simp [X, hj]
          have hle : X (brk T k) ≤ M0 (brk T k) :=
            hM0_ge (t := brk T k) (s := ⟨brk T k, hbk_nonneg⟩) le_rfl
          rw [hX_bk] at hle
          exact hle
        · have hlt : brk T k < c := lt_of_le_of_ne hc1 (Ne.symm heq)
          refine le_of_forall_pos_le_add fun ε hε => ?_
          set u : ℝ := max (brk T k) (c - ε)
          have hu_ge_bk : brk T k ≤ u := le_max_left _ _
          have hu_lt_c : u < c := max_lt hlt (by linarith)
          have hu_lt_next : u < brk T (k + 1) := lt_of_lt_of_le hu_lt_c hc2
          have hu_nonneg : 0 ≤ u := le_trans hbk_nonneg hu_ge_bk
          have hj : jumpCount T u = k :=
            jumpCount_eq_of_brk hStrict hTendsto hu_ge_bk hu_lt_next
          have hXu : X u = u - S k := by simp [X, hj]
          have hle_M0 : X u ≤ M0 c :=
            hM0_ge (t := c) (s := ⟨u, hu_nonneg⟩) hu_lt_c.le
          have hc_sub_le : c - ε ≤ u := le_max_right _ _
          linarith
  have hM_step : ∀ (k : ℕ) (c : ℝ),
      brk T k ≤ c → c ≤ brk T (k + 1) →
      M c = max (M (brk T k)) (c - S k) := by
    intro k c hc1 hc2
    dsimp [M]
    rw [hM0_step k c hc1 hc2, max_assoc]
  have hbrk_le_M : ∀ k : ℕ, brk T k - S k ≤ M (brk T k) := by
    intro k
    have hbk_nonneg : 0 ≤ brk T k := brk_nonneg hT0 hStrict k
    have hlt : brk T k < brk T (k + 1) := by
      cases k with
      | zero => exact hT0
      | succ j => exact hStrict (Nat.lt_succ_self j)
    have hj : jumpCount T (brk T k) = k :=
      jumpCount_eq_of_brk hStrict hTendsto le_rfl hlt
    have hX_bk : X (brk T k) = brk T k - S k := by simp [X, hj]
    have hle : X (brk T k) ≤ M0 (brk T k) :=
      hM0_ge (t := brk T k) (s := ⟨brk T k, hbk_nonneg⟩) le_rfl
    rw [hX_bk] at hle
    exact le_trans hle (le_max_right _ _)
  have hPiece : ∀ (k : ℕ) (c : ℝ),
      brk T k ≤ c → c ≤ brk T (k + 1) →
      (∫ u in (brk T k)..c, ind u ∂volume) = M c - M (brk T k) ∧
        IntervalIntegrable ind volume (brk T k) c := by
    intro k c hc1 hc2
    set a := brk T k
    have ha_nonneg : 0 ≤ a := brk_nonneg hT0 hStrict k
    set u0 := M a + S k
    have ha_le_u0 : a ≤ u0 := by linarith [hbrk_le_M k]
    set v := min u0 c
    have ha_le_v : a ≤ v := le_min ha_le_u0 hc1
    have hv_le_c : v ≤ c := min_le_right _ _
    set g : ℝ → ℝ := (Set.Ioc v c).indicator (fun _ => (1 : ℝ))
    have hg_int : Integrable g volume :=
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne)).integrable_indicator
        measurableSet_Ioc
    have hg_ii : IntervalIntegrable g volume a c := hg_int.intervalIntegrable
    have hAE : ∀ᵐ u ∂volume, u ∈ Set.uIoc a c → ind u = g u := by
      have hne_c : ∀ᵐ u ∂volume, u ≠ c := by
        rw [ae_iff]; simp
      have hne_u0 : ∀ᵐ u ∂volume, u ≠ u0 := by
        rw [ae_iff]; simp
      filter_upwards [hne_c, hne_u0] with u huc huu0 hu_mem
      rw [Set.uIoc_of_le hc1] at hu_mem
      have hua : a < u := hu_mem.1
      have huc_lt : u < c := lt_of_le_of_ne hu_mem.2 huc
      have hu_nonneg : 0 ≤ u := le_trans ha_nonneg hua.le
      have hnn : (Real.toNNReal u : ℝ) = u := Real.coe_toNNReal u hu_nonneg
      have hj : jumpCount T u = k :=
        jumpCount_eq_of_brk hStrict hTendsto hua.le (lt_of_lt_of_le huc_lt hc2)
      have hXu : X u = u - S k := by simp [X, hj]
      have hMu : M u = max (M a) (u - S k) := hM_step k u hua.le (le_trans huc_lt.le hc2)
      have hcond : (M u - X u = 0) ↔ u0 ≤ u := by
        rw [hMu, hXu, sub_eq_zero, max_eq_right_iff]
        constructor <;> intro h <;> dsimp [u0] at * <;> linarith
      have hind_u : ind u = if u0 ≤ u then (1 : ℝ) else 0 := by
        simp only [ind, hnn, hcond]
      rw [hind_u]
      by_cases h : u0 ≤ u
      · have hv_lt : v < u := by
          have hu0_lt : u0 < u := lt_of_le_of_ne h (Ne.symm huu0)
          exact lt_of_le_of_lt (min_le_left _ _) hu0_lt
        have hmem : u ∈ Set.Ioc v c := ⟨hv_lt, huc_lt.le⟩
        simp [g, h, hmem]
      · have hu_lt_u0 : u < u0 := lt_of_not_ge h
        have hnotmem : u ∉ Set.Ioc v c := by
          intro hm
          have hvu : v < u := hm.1
          dsimp [v] at hvu
          rcases min_cases u0 c with ⟨hmin, _⟩ | ⟨hmin, _⟩
          · rw [hmin] at hvu; linarith
          · rw [hmin] at hvu; linarith
        simp [g, h, hnotmem]
    have hind_ii : IntervalIntegrable ind volume a c :=
      hg_ii.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
        (hAE.mono fun u hu hm => (hu hm).symm))
    have hEq_int : (∫ u in a..c, ind u ∂volume) = ∫ u in a..c, g u ∂volume :=
      intervalIntegral.integral_congr_ae hAE
    have hg_val : (∫ u in a..c, g u ∂volume) = c - v := by
      rw [intervalIntegral.integral_of_le hc1]
      dsimp [g]
      rw [setIntegral_indicator measurableSet_Ioc]
      have hsub : Set.Ioc v c ⊆ Set.Ioc a c := Set.Ioc_subset_Ioc_left ha_le_v
      rw [Set.inter_eq_right.mpr hsub, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hv_le_c)]
    have hDiff : c - v = M c - M a := by
      rw [hM_step k c hc1 hc2]
      dsimp [v, u0]
      rcases le_total (M a + S k) c with hle | hle
      · rw [min_eq_left hle, max_eq_right (by linarith)]
        ring
      · rw [min_eq_right hle, max_eq_left (by linarith)]
        ring
    exact ⟨by rw [hEq_int, hg_val, hDiff], hind_ii⟩
  have hToBrk : ∀ N : ℕ,
      (∫ u in (0 : ℝ)..brk T N, ind u ∂volume) = M (brk T N) - w ∧
        IntervalIntegrable ind volume 0 (brk T N) := by
    intro N
    induction N with
    | zero =>
        simp [brk, hM_zero]
    | succ k ih =>
        have hp := hPiece k (brk T (k + 1)) (brk_le_succ hT0 hStrict k) le_rfl
        have hAdd := intervalIntegral.integral_add_adjacent_intervals ih.2 hp.2
        refine ⟨?_, ih.2.trans hp.2⟩
        rw [← hAdd, ih.1, hp.1]
        ring
  intro t
  set N := jumpCount T (t : ℝ)
  have hbt := brk_le_self_lt_succ hStrict hTendsto t.2
  have h1 := hToBrk N
  have h2 := hPiece N (t : ℝ) hbt.1 hbt.2.le
  have hAdd := intervalIntegral.integral_add_adjacent_intervals h1.2 h2.2
  rw [← hAdd, h1.1, h2.1]
  have hCancel : M (brk T N) - w + (M (t : ℝ) - M (brk T N)) = M (t : ℝ) - w := by ring
  rw [hCancel]
  dsimp [M]
  rcases le_total w (M0 (t : ℝ)) with hle | hle
  · rw [max_eq_right hle, max_eq_left (by linarith)]
  · rw [max_eq_left hle, max_eq_right (by linarith)]
    ring

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPositiveClaims : F (Set.Iic (0 : ℝ)) = 0) :
    ∀ w : ℝ, 0 ≤ w →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∫ s in (0 : ℝ)..(t : ℝ),
          (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
            then (1 : ℝ) else 0) ∂volume) =
        max
          ((sSup {x : ℝ | ∃ s : ℝ≥0,
            s ≤ t ∧
              x = riskSurplus arrival claims 1 0 s ω}) - w) 0 := by
  intro w hw
  have hPos := hDriver.ae_interarrival_pos hRate
  have hStrict := hDriver.ae_strictMono_arrival hRate
  have hTendsto := hDriver.ae_tendsto_arrival hRate
  have hClaimsPos : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    have hlaw : P.map (claims n) = F := (hDriver.law_mark n).map_eq
    have hmeas : Measurable (claims n) := hDriver.measurable_mark n
    have hzero : P {ω | claims n ω ≤ 0} = 0 := by
      have hpre : {ω | claims n ω ≤ 0} = claims n ⁻¹' Set.Iic (0 : ℝ) := rfl
      rw [hpre, ← Measure.map_apply hmeas measurableSet_Iic, hlaw, hPositiveClaims]
    rw [ae_iff]
    convert hzero using 2
    ext ω
    simp [not_lt]
  filter_upwards [hPos, hStrict, hTendsto, hClaimsPos] with ω hPosω hStrictω hTendstoω hClaimsω
  have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
    simpa [ProbabilityTheory.arrival] using hPosω 0
  have hDet := regulator_deterministic
    (fun n => ProbabilityTheory.arrival arrival n ω)
    (fun n => claims n ω)
    hT0 hStrictω hTendstoω (fun n => (hClaimsω n).le) w hw
  intro t
  have hSurplus : ∀ s : ℝ≥0,
      riskSurplus arrival claims 1 0 s ω =
        (s : ℝ) - ∑ i ∈ Finset.range
          (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)), claims i ω := by
    intro s
    simp [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
      ProbabilityTheory.piecewisePath]
  have hSetEq : ∀ u : ℝ≥0,
      {x : ℝ | ∃ s : ℝ≥0, s ≤ u ∧ x = riskSurplus arrival claims 1 0 s ω} =
      {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ (u : ℝ) ∧
        x = (s : ℝ) - ∑ i ∈ Finset.range
          (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)), claims i ω} := by
    intro u
    ext x
    simp [hSurplus]
  have hWlEq : ∀ s : ℝ≥0,
      queueWorkload arrival claims w s ω =
        max w (sSup {x : ℝ | ∃ r : ℝ≥0, (r : ℝ) ≤ (s : ℝ) ∧
          x = (r : ℝ) - ∑ i ∈ Finset.range
            (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (r : ℝ)), claims i ω}) -
        ((s : ℝ) - ∑ i ∈ Finset.range
          (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)), claims i ω) := by
    intro s
    simp [queueWorkload, hSetEq s, hSurplus s]
  simpa only [hWlEq, hSetEq t] using hDet t
