-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:29:06.300523+00:00
-- url     : https://prove2.me/submissions/7dc33079-a7a7-43d4-aff8-d473ee927043

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
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory
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

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
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

