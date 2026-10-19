-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:48:57.592713+00:00
-- url     : https://prove2.me/submissions/bea42ed9-aaa4-440d-95f6-a666a966330c

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
theorem h41n_evl (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (eventually_lt_nhds hde)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  refine ⟨min ε 1, lt_min hε one_pos, fun r hr hrR => ?_⟩
  have hrε : dist r 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact lt_of_lt_of_le hrR (min_le_left _ _)
  have h1 := h hrε (Set.mem_Ioi.mpr hr)
  have hlogr : 0 < -Real.log r :=
    neg_pos.mpr (Real.log_neg hr (lt_of_lt_of_le hrR (min_le_right _ _)))
  have hpos : 0 < μ.real (closedBall x r) := by
    have h0 := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    exact ENNReal.toReal_pos h0.ne' (measure_ne_top _ _)
  rw [div_lt_iff₀ hlogr] at h1
  have h2 : Real.log (r^e) < Real.log (μ.real (closedBall x r)) := by
    rw [Real.log_rpow hr]; linarith
  exact ((Real.log_lt_log_iff (by positivity) hpos).mp h2).le


theorem h41n_meas_cb (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    Measurable (fun x => μ.real (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h := measurable_measure_prodMk_left (ν := μ) hs
  exact h.ennreal_toReal


theorem h41n_lums (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  classical
  let E : ℕ → Set ℝ := fun k => {x | ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/((k:ℝ)+1) →
    (q:ℝ)^e ≤ μ.real (closedBall x q)}
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    simp only [E, Set.setOf_forall]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le measurable_const (h41n_meas_cb μ q)
  have hmono : Monotone E := by
    intro k l hkl x hx q hq hql
    apply hx q hq (lt_of_lt_of_le hql _)
    apply one_div_le_one_div_of_le (by positivity)
    have : (k:ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ k, E k := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R, hR, h⟩ := hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hR
    exact Set.mem_iUnion.mpr ⟨k, fun q hq hqk => h q hq (hqk.trans hk)⟩
  have hnull : μ (⋂ k, (E k)ᶜ) = 0 := by
    rw [← Set.compl_iUnion]
    exact ae_iff.mp hcov
  have ht : Tendsto (fun k => μ (E k)ᶜ) atTop (𝓝 (μ (⋂ k, (E k)ᶜ))) :=
    tendsto_measure_iInter_atTop (fun k => (hEm k).compl.nullMeasurableSet)
      (fun k l hkl => Set.compl_subset_compl.mpr (hmono hkl)) ⟨0, measure_ne_top _ _⟩
  rw [hnull] at ht
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨E k, hEm k, ?_, 2/((k:ℝ)+1), by positivity, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal hη.le hk.le
  · intro x hx r hr hrR
    have h1 : r/2 < min r (1/((k:ℝ)+1)) := by
      apply lt_min (by linarith)
      have : r/2 < 1/((k:ℝ)+1) := by
        rw [lt_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hrR
        linarith
      exact this
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    have hq0 : 0 < (q:ℝ) := by linarith
    calc (r/2)^e ≤ (q:ℝ)^e := Real.rpow_le_rpow (by linarith) hq1.le he
      _ ≤ μ.real (closedBall x q) := hx q hq0 (lt_of_lt_of_le hq2 (min_le_right _ _))
      _ ≤ μ.real (Metric.ball x r) :=
          measureReal_mono (Metric.closedBall_subset_ball (lt_of_lt_of_le hq2 (min_le_left _ _)))



theorem h41n_gsc {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by
  rw [Int.card_Icc]
  have hfl1 : (⌊B/s+1⌋ : ℝ) ≤ B/s+1 := Int.floor_le _
  have hfl2 : -B/s - 1 < (⌊-B/s⌋ : ℝ) := by
    have := Int.lt_floor_add_one (-B/s); linarith
  have hBs : 0 ≤ B/s := div_nonneg hB hs.le
  have hle : ⌊-B/s⌋ ≤ ⌊B/s+1⌋ + 1 := by
    have : (⌊-B/s⌋ : ℝ) ≤ ⌊B/s+1⌋ + 1 := by
      have a := Int.floor_le (-B/s)
      have b := Int.lt_floor_add_one (B/s+1)
      have : -B/s = -(B/s) := by ring
      linarith
    exact_mod_cast this
  have hcast : ((⌊B/s+1⌋ + 1 - ⌊-B/s⌋).toNat : ℝ) = ((⌊B/s+1⌋ + 1 - ⌊-B/s⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast]
  push_cast
  have h3 : 3 ≤ 3/s := by rw [le_div_iff₀ hs]; linarith
  have : (2*B+3)/s = 2*(B/s) + 3/s := by field_simp
  rw [this]
  have e : -B/s = -(B/s) := neg_div _ _
  linarith


theorem h41n_card_q2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : Finset ℤ) (x : ℤ → ℝ)
    (r q : ℝ) (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → 2*r ≤ dist (x i) (x j))
    (hq : ∀ i ∈ t, q ≤ μ.real (Metric.ball (x i) r)) : (t.card : ℝ) * q ≤ 1 := by
  have hpd : (↑t : Set ℤ).PairwiseDisjoint (fun i => Metric.ball (x i) r) := by
    intro i hi j hj hij
    exact Metric.ball_disjoint_ball (by linarith [hdisj i hi j hj hij])
  calc (t.card : ℝ) * q = ∑ i ∈ t, q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ t, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ t, Metric.ball (x i) r) :=
        (measureReal_biUnion_finset hpd (fun _ _ => Metric.isOpen_ball.measurableSet)).symm
    _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := by simp


theorem h41n_sum_negMulLog_le (T : Finset ℤ) (m : ℤ → ℝ) (hm : ∀ b ∈ T, 0 ≤ m b) :
    ∑ b ∈ T, Real.negMulLog (m b) ≤
      Real.negMulLog (∑ b ∈ T, m b) + (∑ b ∈ T, m b) * Real.log T.card := by
  rcases T.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hn : (0:ℝ) < T.card := by exact_mod_cast hne.card_pos
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := T) (w := fun _ => (T.card:ℝ)⁻¹) (p := m)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.mpr (hm i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have e : Real.negMulLog ((T.card:ℝ)⁻¹ * ∑ b ∈ T, m b) = (T.card:ℝ)⁻¹ *
      (Real.negMulLog (∑ b ∈ T, m b) + (∑ b ∈ T, m b) * Real.log T.card) := by
    unfold Real.negMulLog
    rcases eq_or_ne (∑ b ∈ T, m b) 0 with h0 | h0
    · rw [h0]; simp
    · rw [Real.log_mul (inv_ne_zero hn.ne') h0, Real.log_inv]; ring
  rw [e] at hJ
  exact le_of_mul_le_mul_left hJ (inv_pos.mpr hn)

theorem h41n_good_labels (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  classical
  have key : ∀ t ⊆ a, (∀ i ∈ t, ∀ j ∈ t, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) →
      (t.card : ℝ) * q ≤ 1 := by
    intro t ht hsep
    apply h41n_card_q2 μ t x (s/2) q _ (fun i hi => hq i (ht hi))
    have sep1 : ∀ i ∈ t, ∀ j ∈ t, i + 2 ≤ j → s ≤ x j - x i := by
      intro i hi j hj h
      have hfi := hx i (ht hi)
      have hfj := hx j (ht hj)
      simp only [label, Int.floor_eq_iff] at hfi hfj
      have h' : (i:ℝ) + 2 ≤ j := by exact_mod_cast h
      have h1 : 1 ≤ x j / s - x i / s := by linarith
      have e : x j - x i = s * (x j / s - x i / s) := by field_simp
      rw [e]; nlinarith
    intro i hi j hj hij
    rw [Real.dist_eq]
    rcases hsep i hi j hj hij with h | h
    · have := sep1 i hi j hj h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have := sep1 j hj i hi h
      rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := key (a.filter (fun i => Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.even_iff] at hi hj
    omega)
  have h2 := key (a.filter (fun i => ¬ Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.not_even_iff] at hi hj
    omega)
  have hc := Finset.card_filter_add_card_filter_not (s := a) (fun i => Even i)
  have hc' : (a.card : ℝ) = ((a.filter (fun i => Even i)).card : ℝ) +
      ((a.filter (fun i => ¬ Even i)).card : ℝ) := by exact_mod_cast hc.symm
  rw [hc', add_mul]
  linarith


theorem h41n_gridle (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u q η : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, q ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 2+Real.log (max 1 (3/q))+
      η*Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) := by
  classical
  set A := Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ with hA_def
  have hu0 := hu.1
  have hu1 := hu.2
  have hLA : ∀ᵐ x ∂μ, label s u x ∈ A := by
    have hI : ∀ᵐ x ∂μ, x ∈ Set.Icc (-B) B := hB
    filter_upwards [hI] with x hx
    rw [hA_def, Finset.mem_Icc]
    unfold label
    constructor
    · apply Int.floor_mono
      have : -B/s ≤ x/s := div_le_div_of_nonneg_right hx.1 hs.le
      linarith
    · apply Int.floor_mono
      have : x/s ≤ B/s := div_le_div_of_nonneg_right hx.2 hs.le
      linarith
  have hgrid : grid μ s u = ∑ b ∈ A, Real.negMulLog (mass μ (label s u) b) := by
    unfold grid entropy
    exact tsum_eq_sum (fun b hb => by
      rw [mass_eq_zero_of_ae μ (label s u) A hLA hb, Real.negMulLog_zero])
  have hsum1 : ∑ b ∈ A, mass μ (label s u) b = 1 :=
    mass_sum μ (label s u) (label_measurable s u) A hLA
  have hmnn : ∀ b, 0 ≤ mass μ (label s u) b := fun b => mass_nonneg _ _ _
  set G := A.filter (fun b => ∃ x ∈ E, label s u x = b) with hG_def
  have hGA : G ⊆ A := Finset.filter_subset _ _
  -- card bound on good labels
  have hGcard : (G.card : ℝ) * q ≤ 3 := by
    let xf : ℤ → ℝ := fun b => if h : ∃ x ∈ E, label s u x = b then h.choose else 0
    have hxf : ∀ b ∈ G, xf b ∈ E ∧ label s u (xf b) = b := by
      intro b hb
      have h : ∃ x ∈ E, label s u x = b := (Finset.mem_filter.mp hb).2
      simp only [xf, dif_pos h]
      exact h.choose_spec
    exact h41n_good_labels μ hs G xf (fun b hb => (hxf b hb).2)
      (fun b hb => hball _ (hxf b hb).1)
  -- bad mass
  have hbad : ∑ b ∈ A \ G, mass μ (label s u) b ≤ η := by
    have hd : (↑(A \ G) : Set ℤ).PairwiseDisjoint (fun b => {x | label s u x = b}) := by
      intro b _ c _ hbc
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hbc (hx.symm.trans hy)
    have hmeas : ∀ b ∈ A \ G, MeasurableSet {x | label s u x = b} :=
      fun b _ => (label_measurable s u) (measurableSet_singleton b)
    calc ∑ b ∈ A \ G, mass μ (label s u) b
        = μ.real (⋃ b ∈ A \ G, {x | label s u x = b}) := by
          rw [measureReal_biUnion_finset hd hmeas]; rfl
      _ ≤ μ.real Eᶜ := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro x hx
          simp only [Set.mem_iUnion] at hx
          obtain ⟨b, hb, hxb⟩ := hx
          intro hxE
          rw [Finset.mem_sdiff] at hb
          exact hb.2 (Finset.mem_filter.mpr ⟨hb.1, x, hxE, hxb⟩)
      _ ≤ η := hη
  have hη0 : 0 ≤ η := le_trans measureReal_nonneg hη
  set P := ∑ b ∈ G, mass μ (label s u) b with hP
  set Q := ∑ b ∈ A \ G, mass μ (label s u) b with hQ
  have hPQ : Q + P = 1 := by
    rw [hP, hQ, Finset.sum_sdiff hGA, hsum1]
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun b _ => hmnn b)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun b _ => hmnn b)
  have h1 := h41n_sum_negMulLog_le G (mass μ (label s u)) (fun b _ => hmnn b)
  have h2 := h41n_sum_negMulLog_le (A \ G) (mass μ (label s u)) (fun b _ => hmnn b)
  rw [← hP] at h1
  rw [← hQ] at h2
  have hbin : Real.negMulLog P + Real.negMulLog Q ≤ Real.log 2 := by
    have := Real.binEntropy_le_log_two (p := P)
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at this
    rwa [show 1 - P = Q by linarith] at this
  have hlogG : P * Real.log G.card ≤ Real.log (max 1 (3/q)) := by
    have hm0 : 0 ≤ Real.log (max 1 (3/q)) := Real.log_nonneg (le_max_left _ _)
    rcases Nat.eq_zero_or_pos G.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero, mul_zero]; exact hm0
    · have hc1 : (1:ℝ) ≤ G.card := by exact_mod_cast h0
      have hl0 : 0 ≤ Real.log G.card := Real.log_nonneg hc1
      have hcq : (G.card:ℝ) ≤ 3/q := by rw [le_div_iff₀ hq]; exact hGcard
      have hl : Real.log G.card ≤ Real.log (max 1 (3/q)) :=
        Real.log_le_log (by linarith) (le_trans hcq (le_max_right _ _))
      have hP1 : P ≤ 1 := by linarith
      nlinarith
  have hlogB : Q * Real.log (A \ G).card ≤ η * Real.log (max 1 (A.card : ℝ)) := by
    have hl0 : 0 ≤ Real.log (A \ G).card := Real.log_natCast_nonneg _
    have hl : Real.log (A \ G).card ≤ Real.log (max 1 (A.card : ℝ)) := by
      rcases Nat.eq_zero_or_pos (A \ G).card with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (le_max_left _ _)
      · have hc1 : (1:ℝ) ≤ (A \ G).card := by exact_mod_cast h0
        apply Real.log_le_log (by linarith)
        apply le_trans _ (le_max_right _ _)
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    calc Q * Real.log (A \ G).card ≤ η * Real.log (A \ G).card :=
          mul_le_mul_of_nonneg_right hbad hl0
      _ ≤ η * Real.log (max 1 (A.card : ℝ)) := mul_le_mul_of_nonneg_left hl hη0
  rw [hgrid, ← Finset.sum_sdiff hGA]
  linarith

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d D : ℝ} (hd : 0 ≤ d) (hD : d < D)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C := by
  obtain ⟨B, hB0, hB⟩ := hc
  set e := (d + D)/2 with he_def
  have hde : d < e := by rw [he_def]; linarith
  have heD : e < D := by rw [he_def]; linarith
  have he0 : 0 ≤ e := by linarith
  set η := D - e with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  have hloc : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
    filter_upwards [hlim, (Measure.support_mem_ae : μ.support ∈ ae μ)] with x hx hxs
    exact h41n_evl μ hxs hde hx
  obtain ⟨E, hEm, hEc, R, hR, hER⟩ := h41n_lums μ he0 hη hloc
  have hB3 : (0:ℝ) < 2*B+3 := by linarith
  set C1 := Real.log 2 + Real.log 3 + e * Real.log 4 + η * Real.log (2*B+3) with hC1
  set C2 := |Real.log 2 + Real.log ((2*B+3)/(2*R))| with hC2
  have hC1nn : 0 ≤ C1 := by
    have h1 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have h2 := Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)
    have h3 := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    have h4 := Real.log_nonneg (show (1:ℝ) ≤ 2*B+3 by linarith)
    have := mul_nonneg he0 h3
    have := mul_nonneg hη.le h4
    rw [hC1]; linarith
  refine ⟨C1 + C2, fun s hs hs1 => ?_⟩
  have hlog1s : 0 < Real.log (1/s) := Real.log_pos (by rw [lt_div_iff₀ hs]; linarith)
  have hcard := h41n_gsc hB0 hs hs1.le
  set N := ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) with hN
  have hlogN : Real.log (max 1 N) ≤ Real.log (2*B+3) + Real.log (1/s) := by
    rw [← Real.log_mul hB3.ne' (by positivity)]
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
    apply max_le
    · rw [mul_one_div, le_div_iff₀ hs]; linarith
    · rw [mul_one_div]; exact hcard
  have hbd : ∀ u ∈ Set.Icc (0:ℝ) 1, grid μ s u ≤ D * Real.log (1/s) + (C1 + C2) := by
    intro u hu
    by_cases hsR : s/2 < R
    · have hq : 0 < (s/4)^e := by positivity
      have hg := h41n_gridle μ hs hq hB hu E hEc (fun x hx => by
        have := hER x hx (s/2) (by positivity) hsR
        rwa [show s/2/2 = s/4 by ring] at this)
      have hq1 : (s/4)^e ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) he0
      have h3q : Real.log (max 1 (3/(s/4)^e)) = Real.log 3 + e * Real.log 4 + e * Real.log (1/s) := by
        rw [max_eq_right (by rw [le_div_iff₀ hq]; linarith), Real.log_div (by norm_num) hq.ne',
          Real.log_rpow (by positivity), show s/4 = (1/s)⁻¹ * 4⁻¹ by field_simp,
          Real.log_mul (by positivity) (by norm_num), Real.log_inv, Real.log_inv]
        ring
      rw [h3q] at hg
      have hC2nn : 0 ≤ C2 := abs_nonneg _
      have : η * Real.log (max 1 N) ≤ η * (Real.log (2*B+3) + Real.log (1/s)) :=
        mul_le_mul_of_nonneg_left hlogN hη.le
      have hD : D = e + η := by rw [hη_def]; ring
      rw [hD]
      nlinarith
    · push_neg at hsR
      have hg := h41n_gridle μ hs (by norm_num : (0:ℝ) < 3) (η := 1) hB hu ∅
        (by simp) (fun x hx => absurd hx (Set.notMem_empty x))
      have h31 : Real.log (max 1 (3/3 : ℝ)) = 0 := by norm_num
      rw [h31, one_mul] at hg
      have h2 : Real.log (max 1 N) ≤ Real.log ((2*B+3)/(2*R)) := by
        apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
        apply max_le
        · rw [le_div_iff₀ (by positivity)]; linarith
        · refine hcard.trans ?_
          apply div_le_div_of_nonneg_left hB3.le (by positivity)
          linarith
      have hC2 : Real.log 2 + Real.log ((2*B+3)/(2*R)) ≤ C2 := le_abs_self _
      have : 0 ≤ D * Real.log (1/s) := mul_nonneg (by linarith) hlog1s.le
      linarith
  have hgnn : ∀ u, 0 ≤ grid μ s u := by
    intro u
    unfold grid entropy
    apply tsum_nonneg
    intro b
    apply Real.negMulLog_nonneg (mass_nonneg _ _ _)
    unfold mass
    exact measureReal_le_one
  have hK : 0 ≤ D * Real.log (1/s) + (C1 + C2) :=
    le_trans (hgnn 0) (hbd 0 ⟨le_rfl, zero_le_one⟩)
  unfold averaged
  calc ∫ u in Set.Icc (0:ℝ) 1, grid μ s u ≤ ‖∫ u in Set.Icc (0:ℝ) 1, grid μ s u‖ :=
        (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ (D * Real.log (1/s) + (C1 + C2)) * volume.real (Set.Icc (0:ℝ) 1) :=
        norm_setIntegral_le_of_norm_le_const (by simp) (fun u hu => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgnn u)]; exact hbd u hu)
    _ = D * Real.log (1/s) + (C1 + C2) := by simp

