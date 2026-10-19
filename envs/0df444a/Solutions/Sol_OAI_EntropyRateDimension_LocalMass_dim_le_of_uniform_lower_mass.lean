-- Prove2me | solution 1 for OAI.EntropyRateDimension.LocalMass.dim_le_of_uniform_lower_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:42:32.422116+00:00
-- url     : https://prove2.me/submissions/88946ea0-bce1-43ae-b752-1601235471ea

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

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureEntropy
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

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) {B e R : ℝ} (he : 0 ≤ e) (hR : 0 < R)
    (hE : E ⊆ Icc (-B) B)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      (r/2)^e ≤ μ.real (ball x r)) : dimH E ≤ ENNReal.ofReal e := by
  classical
  -- scales
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδR : ∀ᶠ n in atTop, δ n < R := hδlim.eventually (eventually_lt_nhds hR)
  let cell : ℕ → ℤ → Set ℝ := fun n j => E ∩ {x | label (δ n) 0 x = j}
  let J : ℕ → Finset ℤ := fun n =>
    (Finset.Icc ⌊-B/(δ n) + 0⌋ ⌊B/(δ n) + 0⌋).filter (fun j => (cell n j).Nonempty)
  let t : ∀ n : ℕ, (J n) → Set ℝ := fun n i => cell n i.1
  have hdiam : ∀ n (i : J n), Metric.ediam (t n i) ≤ ENNReal.ofReal (δ n) := by
    intro n i
    apply Metric.ediam_le
    intro x hx y hy
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hx2 : label (δ n) 0 x = i.1 := hx.2
    have hy2 : label (δ n) 0 y = i.1 := hy.2
    simp only [label, Int.floor_eq_iff] at hx2 hy2
    have h1 : x / δ n - y / δ n < 1 := by linarith
    have h2 : y / δ n - x / δ n < 1 := by linarith
    have hδn : δ n ≠ 0 := (hδpos n).ne'
    have e1 : x - y = δ n * (x / δ n - y / δ n) := by field_simp
    rw [Real.dist_eq, abs_le]
    constructor
    · have := hδpos n; nlinarith
    · have := hδpos n; nlinarith
  have hcover : ∀ n, E ⊆ ⋃ i, t n i := by
    intro n x hx
    have hxB := hE hx
    rw [Set.mem_iUnion]
    have hmem : label (δ n) 0 x ∈ J n := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨x, hx, rfl⟩⟩
      · apply Int.floor_mono
        have := div_le_div_of_nonneg_right hxB.1 (hδpos n).le
        linarith
      · apply Int.floor_mono
        have := div_le_div_of_nonneg_right hxB.2 (hδpos n).le
        linarith
    exact ⟨⟨_, hmem⟩, hx, rfl⟩
  have hcard : ∀ᶠ n in atTop, ((J n).card : ℝ) * (δ n / 4)^e ≤ 3 := by
    filter_upwards [hδR] with n hn
    let xf : ℤ → ℝ := fun j => if h : (cell n j).Nonempty then h.choose else 0
    have hxf : ∀ j ∈ J n, xf j ∈ cell n j := by
      intro j hj
      have h : (cell n j).Nonempty := (Finset.mem_filter.mp hj).2
      simp only [xf, dif_pos h]
      exact h.choose_spec
    have := h41n_good_labels μ (hδpos n) (J n) xf (fun j hj => (hxf j hj).2)
      (fun j hj => by
        have h1 := hball (xf j) (hxf j hj).1 (δ n / 2) (by linarith [hδpos n]) (by linarith [hδpos n])
        rwa [show δ n / 2 / 2 = δ n / 4 by ring] at h1)
    exact this
  have hsum : ∀ᶠ n in atTop, ∑ i, Metric.ediam (t n i) ^ e ≤ ENNReal.ofReal (3 * 4^e) := by
    filter_upwards [hcard] with n hn
    calc ∑ i, Metric.ediam (t n i) ^ e ≤ ∑ _i : J n, ENNReal.ofReal (δ n) ^ e :=
          Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hdiam n i) he
      _ = ENNReal.ofReal ((J n).card * (δ n)^e) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
            ENNReal.ofReal_rpow_of_nonneg (hδpos n).le he, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (3 * 4^e) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.div_rpow (hδpos n).le (by norm_num)] at hn
          have h4 : (0:ℝ) < 4^e := by positivity
          rw [← mul_div_assoc, div_le_iff₀ h4] at hn
          linarith
  have hH : μH[e] E ≤ ENNReal.ofReal (3 * 4^e) := by
    refine le_trans (Measure.hausdorffMeasure_le_liminf_sum e E (fun n => ENNReal.ofReal (δ n))
      (by simpa using ENNReal.tendsto_ofReal hδlim) t
      (Filter.Eventually.of_forall fun n i => hdiam n i)
      (Filter.Eventually.of_forall hcover)) ?_
    exact Filter.liminf_le_of_frequently_le' hsum.frequently
  have he' : ((e.toNNReal : ℝ)) = e := Real.coe_toNNReal _ he
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [he']
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH

