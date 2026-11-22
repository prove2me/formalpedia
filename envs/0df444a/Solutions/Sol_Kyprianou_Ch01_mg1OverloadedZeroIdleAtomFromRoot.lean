-- Prove2me | solution 1 for Kyprianou.Ch01.mg1OverloadedZeroIdleAtomFromRoot
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:45:51.31597+00:00
-- url     : https://prove2.me/submissions/15330b48-ecd0-4876-be84-289df41f9611

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootIff
import Theorems.Thm_Kyprianou_Ch01_queueUpperPassageProbability
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

private def brk (T : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => T k

private lemma brk_nonneg {T : ℕ → ℝ} (hT0 : 0 < T 0) (hStrict : StrictMono T) :
    ∀ k : ℕ, 0 ≤ brk T k
  | 0 => le_rfl
  | k + 1 => le_trans hT0.le (hStrict.monotone (Nat.zero_le k))

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

private lemma totalIdleTime_gt_iff_deterministic
    (T Y : ℕ → ℝ) (hT0 : 0 < T 0) (hStrict : StrictMono T)
    (hTendsto : Tendsto T atTop atTop) (hY : ∀ n, 0 ≤ Y n)
    (w : ℝ) (hw : 0 ≤ w) :
    let S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, Y i
    let X : ℝ → ℝ := fun u => u - S (jumpCount T u)
    let M0 : ℝ → ℝ := fun t => sSup {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)}
    let M : ℝ → ℝ := fun t => max w (M0 t)
    let ind : ℝ → ℝ≥0∞ := fun u =>
      if M (Real.toNNReal u : ℝ) - X (Real.toNNReal u : ℝ) = 0 then (1 : ℝ≥0∞) else 0
    ∀ y : ℝ, 0 ≤ y →
      (ENNReal.ofReal y < ∫⁻ u in Set.Ici (0 : ℝ), ind u ∂volume ↔
        ∃ t : ℝ≥0, 0 < t ∧ w + y < X (t : ℝ)) := by
  intro S X M0 M ind
  have hS_nonneg : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg (fun i _ => hY i)
  have hS_mono : ∀ {j k}, j ≤ k → S j ≤ S k := fun hjk =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) (fun i _ _ => hY i)
  have hX_le : ∀ u : ℝ, X u ≤ u := fun u => by dsimp [X]; linarith [hS_nonneg (jumpCount T u)]
  have hX_zero : X 0 = 0 := by
    have hj0 : jumpCount T 0 = 0 := jumpCount_eq_of_brk hStrict hTendsto (k := 0) le_rfl hT0
    simp [X, S, hj0]
  have hBdd : ∀ t : ℝ, BddAbove {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)} := fun t =>
    ⟨t, by rintro x ⟨s, hs, rfl⟩; exact le_trans (hX_le (s : ℝ)) hs⟩
  have hNonempty : ∀ {t : ℝ}, 0 ≤ t →
      {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ x = X (s : ℝ)}.Nonempty := fun ht =>
    ⟨X 0, ⟨0, ht, rfl⟩⟩
  have hM0_ge : ∀ {t : ℝ} {s : ℝ≥0}, (s : ℝ) ≤ t → X (s : ℝ) ≤ M0 t := fun hs =>
    le_csSup (hBdd _) ⟨_, hs, rfl⟩
  have hM0_mono : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ → M0 t₁ ≤ M0 t₂ := fun ht₁ hle =>
    csSup_le_csSup (hBdd _) (hNonempty ht₁) (by rintro x ⟨s, hs, rfl⟩; exact ⟨s, le_trans hs hle, rfl⟩)
  have hM0_zero : M0 0 = 0 := by
    apply le_antisymm
    · refine csSup_le (hNonempty le_rfl) ?_
      rintro x ⟨s, hs, rfl⟩
      rw [le_antisymm hs s.2, hX_zero]
    · have h0 : X 0 ≤ M0 0 := hM0_ge (t := 0) (s := 0) le_rfl
      rwa [hX_zero] at h0
  have hM_zero : M 0 = w := by dsimp [M]; rw [hM0_zero]; exact max_eq_left hw
  have hM_mono : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ → M t₁ ≤ M t₂ := fun ht₁ hle =>
    max_le_max_left w (hM0_mono ht₁ hle)
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
      · have hsb' : brk T k < (s : ℝ) := lt_of_not_ge hsb
        by_cases hslt : (s : ℝ) < brk T (k + 1)
        · have hj : jumpCount T (s : ℝ) = k :=
            jumpCount_eq_of_brk hStrict hTendsto hsb'.le hslt
          have hXs : X (s : ℝ) = (s : ℝ) - S k := by simp [X, hj]
          rw [hXs]
          exact le_trans (by linarith) (le_max_right _ _)
        · have hslt' : brk T (k + 1) ≤ (s : ℝ) := le_of_not_gt hslt
          have hceq : c = brk T (k + 1) := le_antisymm hc2 (le_trans hslt' hs)
          have hj_ge : k ≤ jumpCount T (s : ℝ) := by
            cases k with
            | zero => exact Nat.zero_le _
            | succ j =>
                have : j < jumpCount T (s : ℝ) := by
                  rw [lt_jumpCount_iff hStrict hTendsto]
                  dsimp [brk] at hsb'
                  exact hsb'.le
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
          have hlt : brk T k < brk T (k + 1) := by
            cases k with
            | zero => exact hT0
            | succ j => exact hStrict (Nat.lt_succ_self j)
          have hj := jumpCount_eq_of_brk hStrict hTendsto le_rfl hlt
          have hX_bk : X (brk T k) = brk T k - S k := by simp [X, hj]
          have hle : X (brk T k) ≤ M0 (brk T k) :=
            hM0_ge (t := brk T k) (s := ⟨brk T k, hbk_nonneg⟩) le_rfl
          rwa [hX_bk] at hle
        · have hlt : brk T k < c := lt_of_le_of_ne hc1 (Ne.symm heq)
          refine le_of_forall_pos_le_add fun ε hε => ?_
          set u : ℝ := max (brk T k) (c - ε)
          have hu_ge_bk : brk T k ≤ u := le_max_left _ _
          have hu_lt_c : u < c := max_lt hlt (by linarith)
          have hu_lt_next : u < brk T (k + 1) := lt_of_lt_of_le hu_lt_c hc2
          have hu_nonneg : 0 ≤ u := le_trans hbk_nonneg hu_ge_bk
          have hj := jumpCount_eq_of_brk hStrict hTendsto hu_ge_bk hu_lt_next
          have hXu : X u = u - S k := by simp [X, hj]
          have hle_M0 : X u ≤ M0 c :=
            hM0_ge (t := c) (s := ⟨u, hu_nonneg⟩) hu_lt_c.le
          have hc_sub_le : c - ε ≤ u := le_max_right _ _
          linarith
  have hM_step : ∀ (k : ℕ) (c : ℝ),
      brk T k ≤ c → c ≤ brk T (k + 1) →
      M c = max (M (brk T k)) (c - S k) := fun k c hc1 hc2 => by
    dsimp [M]; rw [hM0_step k c hc1 hc2, max_assoc]
  have hbrk_le_M : ∀ k : ℕ, brk T k - S k ≤ M (brk T k) := by
    intro k
    have hbk_nonneg : 0 ≤ brk T k := brk_nonneg hT0 hStrict k
    have hlt : brk T k < brk T (k + 1) := by
      cases k with
      | zero => exact hT0
      | succ j => exact hStrict (Nat.lt_succ_self j)
    have hj := jumpCount_eq_of_brk hStrict hTendsto le_rfl hlt
    have hX_bk : X (brk T k) = brk T k - S k := by simp [X, hj]
    have hle : X (brk T k) ≤ M0 (brk T k) :=
      hM0_ge (t := brk T k) (s := ⟨brk T k, hbk_nonneg⟩) le_rfl
    rw [hX_bk] at hle
    exact le_trans hle (le_max_right _ _)
  have hPiece : ∀ k : ℕ,
      (∫⁻ u in Set.Ioc (brk T k) (brk T (k + 1)), ind u ∂volume) =
        ENNReal.ofReal (M (brk T (k + 1)) - M (brk T k)) := by
    intro k
    set a := brk T k
    set c := brk T (k + 1)
    have hc1 : a ≤ c := brk_le_succ hT0 hStrict k
    have ha_nonneg : 0 ≤ a := brk_nonneg hT0 hStrict k
    set u0 := M a + S k
    have ha_le_u0 : a ≤ u0 := by linarith [hbrk_le_M k]
    set v := min u0 c
    have ha_le_v : a ≤ v := le_min ha_le_u0 hc1
    have hv_le_c : v ≤ c := min_le_right _ _
    set g : ℝ → ℝ≥0∞ := (Set.Ioc v c).indicator (fun _ => (1 : ℝ≥0∞))
    have hAE : ind =ᵐ[volume.restrict (Set.Ioc a c)] g := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      have hne_c : ∀ᵐ u ∂volume, u ≠ c := by rw [ae_iff]; simp
      have hne_u0 : ∀ᵐ u ∂volume, u ≠ u0 := by rw [ae_iff]; simp
      filter_upwards [hne_c, hne_u0] with u huc huu0 hu_mem
      have hua : a < u := hu_mem.1
      have huc_lt : u < c := lt_of_le_of_ne hu_mem.2 huc
      have hu_nonneg : 0 ≤ u := le_trans ha_nonneg hua.le
      have hnn : (Real.toNNReal u : ℝ) = u := Real.coe_toNNReal u hu_nonneg
      have hj : jumpCount T u = k := jumpCount_eq_of_brk hStrict hTendsto hua.le huc_lt
      have hXu : X u = u - S k := by simp [X, hj]
      have hMu : M u = max (M a) (u - S k) := hM_step k u hua.le huc_lt.le
      have hcond : (M u - X u = 0) ↔ u0 ≤ u := by
        rw [hMu, hXu, sub_eq_zero, max_eq_right_iff]
        constructor <;> intro h <;> dsimp [u0] at * <;> linarith
      have hind_u : ind u = if u0 ≤ u then (1 : ℝ≥0∞) else 0 := by
        simp only [ind, hnn, hcond]
      rw [hind_u]
      by_cases h : u0 ≤ u
      · have hv_lt : v < u :=
          lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_ne h (Ne.symm huu0))
        have hmem : u ∈ Set.Ioc v c := ⟨hv_lt, huc_lt.le⟩
        simp [g, h, hmem]
      · have hu_lt_u0 : u < u0 := lt_of_not_ge h
        have hnotmem : u ∉ Set.Ioc v c := by
          intro hm
          have hvu : v < u := hm.1
          dsimp [v] at hvu
          rcases min_cases u0 c with ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> linarith
        simp [g, h, hnotmem]
    rw [lintegral_congr_ae hAE]
    dsimp [g]
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc_left ha_le_v), setLIntegral_one, Real.volume_Ioc]
    congr 1
    rw [hM_step k c hc1 le_rfl]
    dsimp [v, u0]
    rcases le_total (M a + S k) c with hle | hle
    · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
    · rw [min_eq_right hle, max_eq_left (by linarith)]; ring
  have hToBrk : ∀ N : ℕ,
      (∫⁻ u in Set.Ioc (0 : ℝ) (brk T N), ind u ∂volume) =
        ENNReal.ofReal (M (brk T N) - w) := by
    intro N
    induction N with
    | zero =>
        simp [brk, hM_zero]
    | succ k ih =>
        have hbk_nn : 0 ≤ brk T k := brk_nonneg hT0 hStrict k
        have hbk_le : brk T k ≤ brk T (k + 1) := brk_le_succ hT0 hStrict k
        have hUnion : Set.Ioc (0 : ℝ) (brk T (k + 1)) =
            Set.Ioc (0 : ℝ) (brk T k) ∪ Set.Ioc (brk T k) (brk T (k + 1)) :=
          (Set.Ioc_union_Ioc_eq_Ioc hbk_nn hbk_le).symm
        have hDisj : Disjoint (Set.Ioc (0 : ℝ) (brk T k)) (Set.Ioc (brk T k) (brk T (k + 1))) :=
          Set.Ioc_disjoint_Ioc_of_le le_rfl
        rw [hUnion, lintegral_union measurableSet_Ioc hDisj, ih, hPiece k,
          ← ENNReal.ofReal_add (sub_nonneg.mpr (by rw [← hM_zero]; exact hM_mono le_rfl hbk_nn))
            (sub_nonneg.mpr (hM_mono hbk_nn hbk_le))]
        congr 1
        ring
  have hIdle_eq_iSup :
      (∫⁻ u in Set.Ici (0 : ℝ), ind u ∂volume) =
        ⨆ N : ℕ, ENNReal.ofReal (M (brk T N) - w) := by
    have hIci_Ioi : (∫⁻ u in Set.Ici (0 : ℝ), ind u ∂volume) =
        ∫⁻ u in Set.Ioi (0 : ℝ), ind u ∂volume := by
      have hEqSet : Set.Ici (0 : ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) := Ioi_ae_eq_Ici.symm
      rw [Measure.restrict_congr_set hEqSet]
    rw [hIci_Ioi]
    have hBrk_strict : StrictMono (brk T) := by
      intro i j hij
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ m =>
              dsimp [brk]
              exact lt_of_lt_of_le hT0 (hStrict.monotone (Nat.zero_le m))
      | succ n =>
          cases j with
          | zero => omega
          | succ m =>
              dsimp [brk]
              exact hStrict (by omega)
    have hUnion : Set.Ioi (0 : ℝ) = ⋃ k : ℕ, Set.Ioc (brk T k) (brk T (k + 1)) := by
      ext u
      simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · intro hu
        have hEv := hTendsto.eventually (Filter.eventually_ge_atTop u)
        rw [Filter.eventually_atTop] at hEv
        obtain ⟨N, hN⟩ := hEv
        have hne : ({n : ℕ | u ≤ T n}).Nonempty := ⟨N, hN N le_rfl⟩
        set k := sInf {n : ℕ | u ≤ T n}
        have hk_mem : u ≤ T k := Nat.sInf_mem hne
        refine ⟨k, ?_, hk_mem⟩
        cases hk : k with
        | zero => simpa [brk] using hu
        | succ j =>
            dsimp [brk]
            by_contra hle
            have hle' : u ≤ T j := le_of_not_gt hle
            have hinf := Nat.sInf_le (s := {n : ℕ | u ≤ T n}) hle'
            omega
      · rintro ⟨k, h1, _⟩
        exact lt_of_le_of_lt (brk_nonneg hT0 hStrict k) h1
    have hDisj : Pairwise (fun i j => Disjoint (Set.Ioc (brk T i) (brk T (i + 1)))
        (Set.Ioc (brk T j) (brk T (j + 1)))) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact Set.Ioc_disjoint_Ioc_of_le (hBrk_strict.monotone (Nat.succ_le_of_lt hlt))
      · exact (Set.Ioc_disjoint_Ioc_of_le (hBrk_strict.monotone (Nat.succ_le_of_lt hgt))).symm
    rw [hUnion, lintegral_iUnion (fun _ => measurableSet_Ioc) hDisj, ENNReal.tsum_eq_iSup_nat]
    congr 1
    ext N
    have hSum : ∑ k ∈ Finset.range N, (∫⁻ u in Set.Ioc (brk T k) (brk T (k + 1)), ind u ∂volume) =
        ENNReal.ofReal (M (brk T N) - w) := by
      induction N with
      | zero => simp [brk, hM_zero]
      | succ k ih =>
          rw [Finset.sum_range_succ, ih, hPiece k]
          have hbk_nn : 0 ≤ brk T k := brk_nonneg hT0 hStrict k
          have hbk_le : brk T k ≤ brk T (k + 1) := brk_le_succ hT0 hStrict k
          rw [← ENNReal.ofReal_add (sub_nonneg.mpr (by rw [← hM_zero]; exact hM_mono le_rfl hbk_nn))
            (sub_nonneg.mpr (hM_mono hbk_nn hbk_le))]
          congr 1
          ring
    exact hSum
  intro y hy
  rw [hIdle_eq_iSup, lt_iSup_iff]
  constructor
  · rintro ⟨N, hN⟩
    have hlt : y < M (brk T N) - w := by
      by_contra hle
      push Not at hle
      exact not_lt_of_ge (ENNReal.ofReal_le_ofReal hle) hN
    have hltM0 : w + y < M0 (brk T N) := by
      dsimp [M] at hlt
      rcases le_total w (M0 (brk T N)) with h | h
      · rw [max_eq_right h] at hlt; linarith
      · rw [max_eq_left h] at hlt; linarith
    have hEx : ∃ x ∈ {x : ℝ | ∃ s : ℝ≥0, (s : ℝ) ≤ brk T N ∧ x = X (s : ℝ)}, w + y < x :=
      exists_lt_of_lt_csSup (hNonempty (brk_nonneg hT0 hStrict N)) hltM0
    obtain ⟨_, ⟨t, _, rfl⟩, htx⟩ := hEx
    have ht_pos : 0 < t := by
      by_contra ht0
      have hteq : t = 0 := le_antisymm (le_of_not_gt ht0) t.2
      rw [hteq] at htx
      simp [hX_zero] at htx
      linarith
    exact ⟨t, ht_pos, htx⟩
  · rintro ⟨t, _, htx⟩
    have hEv := hTendsto.eventually (Filter.eventually_ge_atTop (t : ℝ))
    rw [Filter.eventually_atTop] at hEv
    obtain ⟨N, hN⟩ := hEv
    refine ⟨N + 1, ?_⟩
    have hleM0 : X (t : ℝ) ≤ M0 (brk T (N + 1)) := hM0_ge (hN N le_rfl)
    have hlt : y < M (brk T (N + 1)) - w := by
      dsimp [M]
      have : M0 (brk T (N + 1)) ≤ max w (M0 (brk T (N + 1))) := le_max_right _ _
      linarith
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt

private lemma measurable_riskSurplus_fixed
    {Ω : Type u} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (hArr : ∀ n, Measurable (arrival n))
    (hClm : ∀ n, Measurable (claims n))
    (t : ℝ≥0) :
    Measurable (fun ω => riskSurplus arrival claims 1 0 t ω) := by
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
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq,
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
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
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
  have hEq : (fun ω => riskSurplus arrival claims 1 0 t ω) =
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
    (theta : ℝ) (htheta : 0 < theta)
    (hroot : queueLaplaceExponent rate F theta = 0) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
        1 - Real.exp (-theta * w) := by
  intro w hw
  have hOverload : 1 < (rate : ℝ) * mu :=
    (Kyprianou.Ch01.queueLaplaceExponent_rootIff rate hrate F hclaimpos hclaimint mu hmu hmean).mp
      ⟨theta, htheta, hroot⟩
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
  have hIff_ae : ∀ᵐ ω ∂P,
      (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ↔
        ∃ t : ℝ≥0, 0 < t ∧ w < riskSurplus arrival claims 1 0 t ω := by
    filter_upwards [hPos, hStrict, hTendsto, hClaimsPos] with ω hPosω hStrictω hTendstoω hClaimsω
    have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
      simpa [ProbabilityTheory.arrival] using hPosω 0
    have hDet := totalIdleTime_gt_iff_deterministic
      (fun n => ProbabilityTheory.arrival arrival n ω)
      (fun n => claims n ω)
      hT0 hStrictω hTendstoω (fun n => (hClaimsω n).le) w hw 0 le_rfl
    have hSurplus : ∀ s : ℝ≥0,
        riskSurplus arrival claims 1 0 s ω =
          (s : ℝ) - ∑ i ∈ Finset.range
            (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)), claims i ω := by
      intro s
      simp [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
        ProbabilityTheory.piecewisePath]
    have hSetEq : ∀ s : ℝ≥0,
        {x : ℝ | ∃ r : ℝ≥0, r ≤ s ∧ x = riskSurplus arrival claims 1 0 r ω} =
        {x : ℝ | ∃ r : ℝ≥0, (r : ℝ) ≤ (s : ℝ) ∧
          x = (r : ℝ) - ∑ i ∈ Finset.range
            (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (r : ℝ)), claims i ω} := by
      intro s; ext x; simp [hSurplus]
    have hWlEq : ∀ s : ℝ≥0,
        queueWorkload arrival claims w s ω =
          max w (sSup {x : ℝ | ∃ r : ℝ≥0, (r : ℝ) ≤ (s : ℝ) ∧
            x = (r : ℝ) - ∑ i ∈ Finset.range
              (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (r : ℝ)), claims i ω}) -
          ((s : ℝ) - ∑ i ∈ Finset.range
            (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (s : ℝ)), claims i ω) := by
      intro s; simp [queueWorkload, hSetEq s, hSurplus s]
    simpa only [totalIdleTime, hWlEq, hSurplus, ENNReal.ofReal_zero, add_zero] using hDet
  by_cases hw0 : w = 0
  · subst hw0
    have hZero : ∀ᵐ ω ∂P, totalIdleTime arrival claims 0 ω ≠ 0 := by
      filter_upwards [hPos, hStrict, hTendsto, hIff_ae] with ω hPosω hStrictω hTendstoω hIffω
      have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
        simpa [ProbabilityTheory.arrival] using hPosω 0
      set tR : ℝ := ProbabilityTheory.arrival arrival 0 ω / 2
      have htR_pos : 0 < tR := by positivity
      set t : ℝ≥0 := ⟨tR, htR_pos.le⟩
      have hjc0 : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) tR = 0 :=
        jumpCount_eq_of_brk hStrictω hTendstoω (k := 0) htR_pos.le (by dsimp [brk, tR]; linarith)
      have hpos_val : 0 < riskSurplus arrival claims 1 0 t ω := by
        have hcoe : (t : ℝ) = tR := rfl
        rw [riskSurplus, aggregateClaims, ProbabilityTheory.compoundPoisson,
          ProbabilityTheory.piecewisePath, hcoe, hjc0]
        simpa using htR_pos
      have hgt : (0 : ℝ≥0∞) < totalIdleTime arrival claims 0 ω :=
        hIffω.mpr ⟨t, NNReal.coe_pos.mp htR_pos, hpos_val⟩
      exact hgt.ne'
    have hP0 : P {ω | totalIdleTime arrival claims 0 ω = 0} = 0 := by
      rw [ae_iff] at hZero
      convert hZero using 2
      ext ω; simp
    simp [hP0]
  · have hw_pos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    set A : Set Ω := {ω | ∃ t : ℝ≥0, 0 < t ∧ w < riskSurplus arrival claims 1 0 t ω}
    set Arat : Set Ω := ⋃ q : {q : ℚ // (0 : ℚ) < q},
      {ω | w < riskSurplus arrival claims 1 0 ⟨(q.1 : ℝ), by exact_mod_cast q.2.le⟩ ω}
    have hArat_meas : MeasurableSet Arat :=
      MeasurableSet.iUnion fun q =>
        measurableSet_lt measurable_const
          (measurable_riskSurplus_fixed arrival claims hd.measurable_interarrival
            hd.measurable_mark _)
    have hA_eq_Arat : A =ᵐ[P] Arat := by
      filter_upwards [hPos, hStrict, hTendsto] with ω hPosω hStrictω hTendstoω
      change (ω ∈ A) = (ω ∈ Arat)
      apply propext
      constructor
      · rintro ⟨t, ht_pos, hwt⟩
        have hT0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
          simpa [ProbabilityTheory.arrival] using hPosω 0
        set T := fun n => ProbabilityTheory.arrival arrival n ω
        set k := jumpCount T (t : ℝ)
        have hlt_next : (t : ℝ) < brk T (k + 1) := by
          dsimp [brk]
          have hnot : ¬ (k < jumpCount T (t : ℝ)) := by omega
          rw [lt_jumpCount_iff hStrictω hTendstoω] at hnot
          exact lt_of_not_ge hnot
        have hge_cur : brk T k ≤ (t : ℝ) := by
          cases hk : k with
          | zero => simpa [brk] using t.2
          | succ j =>
              dsimp [brk]
              have hj : j < jumpCount T (t : ℝ) := by omega
              exact (lt_jumpCount_iff hStrictω hTendstoω j (t : ℝ)).mp hj
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt_next
        have hq_pos : (0 : ℚ) < q := by
          have : (0 : ℝ) < (q : ℝ) := lt_trans (NNReal.coe_pos.mpr ht_pos) hq1
          exact_mod_cast this
        rw [Set.mem_iUnion]
        refine ⟨⟨q, hq_pos⟩, ?_⟩
        have hjq : jumpCount T (q : ℝ) = k :=
          jumpCount_eq_of_brk hStrictω hTendstoω (le_trans hge_cur hq1.le) hq2
        have hq_val : riskSurplus arrival claims 1 0 ⟨(q : ℝ), by exact_mod_cast hq_pos.le⟩ ω =
            riskSurplus arrival claims 1 0 t ω + ((q : ℝ) - (t : ℝ)) := by
          unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson
            ProbabilityTheory.piecewisePath
          change 0 + 1 * (q : ℝ) - (0 + 0 * (q : ℝ) + ∑ i ∈ Finset.range (jumpCount T (q : ℝ)), claims i ω) =
            0 + 1 * (t : ℝ) - (0 + 0 * (t : ℝ) + ∑ i ∈ Finset.range k, claims i ω) + ((q : ℝ) - (t : ℝ))
          rw [hjq]
          ring
        change w < riskSurplus arrival claims 1 0 ⟨(q : ℝ), by exact_mod_cast hq_pos.le⟩ ω
        rw [hq_val]
        linarith
      · intro h
        rw [Set.mem_iUnion] at h
        obtain ⟨⟨q, hq_pos⟩, hmem⟩ := h
        have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
        exact ⟨⟨(q : ℝ), hqR_pos.le⟩, NNReal.coe_pos.mp hqR_pos, hmem⟩
    have hZero_eq_compl : {ω | totalIdleTime arrival claims w ω = 0} =ᵐ[P] Aratᶜ := by
      filter_upwards [hIff_ae, hA_eq_Arat] with ω hIffω hAω
      change (totalIdleTime arrival claims w ω = 0) = (ω ∉ Arat)
      have hA_iff : (ω ∈ A) ↔ (ω ∈ Arat) := by
        have := hAω
        exact eq_iff_iff.mp this
      rw [← hA_iff]
      apply propext
      constructor
      · intro h0 hA
        have hgt := hIffω.mpr hA
        rw [h0] at hgt
        exact lt_irrefl _ hgt
      · intro hnA
        by_contra hne
        exact hnA (hIffω.mp (pos_iff_ne_zero.mpr hne))
    have hP_A : (P A).toReal = Real.exp (-theta * w) :=
      Kyprianou.Ch01.queueUpperPassageProbability P arrival claims rate hrate F hd hclaimpos
        hclaimint mu hmean hOverload theta htheta hroot w hw_pos
    have hP_Arat_eq : P Arat = P A := (measure_congr hA_eq_Arat).symm
    have hP_Arat_toReal : (P Arat).toReal = Real.exp (-theta * w) := by
      rw [hP_Arat_eq, hP_A]
    have hP_compl : P {ω | totalIdleTime arrival claims w ω = 0} = 1 - P Arat := by
      rw [measure_congr hZero_eq_compl]
      exact prob_compl_eq_one_sub hArat_meas
    rw [hP_compl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one, hP_Arat_toReal]
