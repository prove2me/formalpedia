-- Prove2me | solution 1 for LookbackMOT.HL.eq_3_28
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:25:17.782538+00:00
-- url     : https://prove2.me/submissions/5e8b0064-73cc-4a35-b5d2-e3c4d7171c46

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL Filter Topology
open scoped NNReal ENNReal

theorem solution (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (m : ℝ) (hm : X₀ ≤ m) :
    (⨅ ξ : Set.Iio m, phi μ X₀ ξ m) = (⨅ ξ : Set.Iio m, callPrice μ ξ / (m - ξ)) ∧
      ((X₀ < m ∨ ∃ a : ℝ, μ (Set.Iio a) = 0) → 0 < μ (Set.Ioi m) →
        ∃ β : ℝ, IsGreatest {ξ : ℝ | ξ < m ∧
            ∀ η : ℝ, η < m → callPrice μ ξ / (m - ξ) ≤ callPrice μ η / (m - η)} β ∧
          (⨅ ξ : Set.Iio m, callPrice μ ξ / (m - ξ)) = callPrice μ β / (m - β)) := by
  have hind : (if m < X₀ then (1:ℝ) else 0) = 0 := if_neg (not_lt.mpr hm)
  refine ⟨?_, ?_⟩
  · congr 1
    ext ξ
    simp only [phi, hind, mul_zero, sub_zero]
  intro hcase hpos
  -- basic facts on the call price
  set c := callPrice μ with hcdef
  have hint : ∀ ξ : ℝ, Integrable (fun y : ℝ => y - ξ) μ := fun ξ =>
    (hμ1.sub (integrable_const ξ))
  have hlin : ∀ ξ : ℝ, ∫ y, (y - ξ) ∂μ = X₀ - ξ := by
    intro ξ
    have := integral_sub hμ1 (integrable_const ξ) (μ := μ)
    simp only [id] at this
    rw [this, hmean]
    simp
  have hcint : ∀ ξ : ℝ, Integrable (fun y : ℝ => max (y - ξ) 0) μ := fun ξ => (hint ξ).pos_part
  have hputint : ∀ ξ : ℝ, Integrable (fun y : ℝ => max (ξ - y) 0) μ := fun ξ =>
    ((integrable_const ξ).sub hμ1).pos_part
  set p : ℝ → ℝ := fun ξ => ∫ y, max (ξ - y) 0 ∂μ with hpdef
  have hcdec : ∀ ξ : ℝ, c ξ = (X₀ - ξ) + p ξ := by
    intro ξ
    simp only [c, p, callPrice]
    rw [← hlin ξ, ← integral_add (hint ξ) (hputint ξ)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only
    rcases le_total y ξ with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hp_nn : ∀ ξ, 0 ≤ p ξ := fun ξ => integral_nonneg (fun y => le_max_right _ _)
  have hc_anti : ∀ x y : ℝ, x ≤ y → c y ≤ c x := by
    intro x y hxy
    exact integral_mono (hcint y) (hcint x) (fun z => max_le_max (by linarith) le_rfl)
  have hc_lip : ∀ x y : ℝ, |c x - c y| ≤ |x - y| := by
    intro x y
    simp only [c, callPrice]
    rw [← integral_sub (hcint x) (hcint y)]
    calc |∫ z, (max (z - x) 0 - max (z - y) 0) ∂μ|
        ≤ ∫ z, |max (z - x) 0 - max (z - y) 0| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, |x - y| ∂μ := by
          apply integral_mono ((hcint x).sub (hcint y)).abs (integrable_const _)
          intro z
          have := abs_max_sub_max_le_max (z - x) 0 (z - y) 0
          simp only at this ⊢
          calc |max (z - x) 0 - max (z - y) 0| ≤ max |z - x - (z - y)| |(0:ℝ) - 0| := this
            _ = |x - y| := by
                rw [sub_self, abs_zero, max_eq_left (abs_nonneg _),
                  show z - x - (z - y) = -(x - y) by ring, abs_neg]
      _ = |x - y| := by simp
  have hc_cont : Continuous c := by
    apply Metric.continuous_iff.mpr
    intro b ε hε
    refine ⟨ε, hε, fun a ha => ?_⟩
    rw [Real.dist_eq] at ha ⊢
    exact lt_of_le_of_lt (hc_lip a b) ha
  have hcm_pos : 0 < c m := by
    simp only [c, callPrice]
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (y - m) 0)
      (fun y => le_max_right _ _) (hcint m)]
    have : Function.support (fun y : ℝ => max (y - m) 0) = Set.Ioi m := by
      ext y
      simp only [Function.mem_support, Set.mem_Ioi, ne_eq]
      constructor
      · intro h; by_contra h'; push_neg at h'; exact h (max_eq_right (by linarith))
      · intro h; rw [max_eq_left (by linarith)]; linarith
    rw [this]; exact hpos
  set k : ℝ → ℝ := fun ξ => c ξ / (m - ξ) with hkdef
  have hk_cont : ContinuousOn k (Set.Iio m) := by
    apply hc_cont.continuousOn.div (continuous_const.sub continuous_id).continuousOn
    intro x hx; have : x < m := hx; exact (sub_pos.mpr this).ne'
  have hk_pos : ∀ ξ, ξ < m → 0 < k ξ := fun ξ hξ =>
    div_pos (lt_of_lt_of_le hcm_pos (hc_anti ξ m hξ.le)) (by linarith)
  -- a reference point ξ₁ and a left cut-off A
  obtain ⟨ξ₁, A, hξ₁m, hAξ₁, hleft⟩ : ∃ ξ₁ A : ℝ, ξ₁ < m ∧ A ≤ ξ₁ ∧ ∀ ξ, ξ < A → k ξ₁ ≤ k ξ := by
    rcases hcase with hlt | ⟨a, ha⟩
    · -- p(ξ) → 0 as ξ → -∞
      have hp_lim : Tendsto p atBot (𝓝 0) := by
        have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atBot)
          (F := fun ξ y => max (ξ - y) 0) (f := fun _ => (0:ℝ))
          (fun y => max (X₀ - y) 0)
          (Eventually.of_forall fun ξ => (hputint ξ).aestronglyMeasurable)
          (by
            filter_upwards [eventually_le_atBot X₀] with ξ hξ
            refine Eventually.of_forall fun y => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
            exact max_le_max (by linarith) le_rfl)
          (hputint X₀)
          (Eventually.of_forall fun y => by
            apply tendsto_const_nhds.congr'
            filter_upwards [eventually_le_atBot y] with ξ hξ
            exact (max_eq_right (by linarith)).symm)
        simpa using this
      have hgap : 0 < (m - X₀) / 2 := by linarith
      obtain ⟨ξ₁, hξ₁p, hξ₁m⟩ :=
        ((hp_lim.eventually (gt_mem_nhds hgap)).and (eventually_lt_atBot m)).exists
      refine ⟨ξ₁, 2 * ξ₁ - m, hξ₁m, by linarith, fun ξ hξ => ?_⟩
      simp only [k]
      have h1 : 0 < m - ξ₁ := by linarith
      have h2 : 0 < m - ξ := by linarith
      rw [div_le_div_iff₀ h1 h2, hcdec, hcdec]
      have := hp_nn ξ
      nlinarith
    · set ξ₁ := min a m - 1
      have hξ₁a : ξ₁ ≤ a := by simp only [ξ₁]; linarith [min_le_left a m]
      have hξ₁m : ξ₁ < m := by simp only [ξ₁]; linarith [min_le_right a m]
      have hae : ∀ᵐ y ∂μ, a ≤ y := by
        rw [ae_iff]
        have : {y : ℝ | ¬ a ≤ y} = Set.Iio a := by ext; simp
        rw [this, ha]
      have hp0 : ∀ ξ, ξ ≤ a → p ξ = 0 := by
        intro ξ hξ
        simp only [p]
        rw [integral_congr_ae (g := fun _ => (0:ℝ))]
        · simp
        · filter_upwards [hae] with y hy
          exact max_eq_right (by linarith)
      refine ⟨ξ₁, ξ₁, hξ₁m, le_rfl, fun ξ hξ => ?_⟩
      simp only [k]
      have h1 : 0 < m - ξ₁ := by linarith
      have h2 : 0 < m - ξ := by linarith
      rw [div_le_div_iff₀ h1 h2, hcdec, hcdec, hp0 ξ₁ hξ₁a, hp0 ξ (by linarith)]
      nlinarith
  -- right cut-off B
  have hkξ₁ := hk_pos ξ₁ hξ₁m
  set B : ℝ := m - c m / (2 * k ξ₁) with hBdef
  have hcm2 : 0 < c m / (2 * k ξ₁) := div_pos hcm_pos (by linarith)
  have hBm : B < m := by simp only [B]; linarith
  have hξ₁B : ξ₁ < B := by
    have hk1 : c m / (m - ξ₁) ≤ k ξ₁ :=
      div_le_div_of_nonneg_right (hc_anti ξ₁ m hξ₁m.le) (by linarith)
    have h1 : 0 < m - ξ₁ := by linarith
    rw [div_le_iff₀ h1] at hk1
    have : c m / (2 * k ξ₁) < m - ξ₁ := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    simp only [B]
    linarith
  have hright : ∀ ξ, B < ξ → ξ < m → k ξ₁ < k ξ := by
    intro ξ hBξ hξm
    have h2 : 0 < m - ξ := by linarith
    have hlow : c m / (m - ξ) ≤ k ξ :=
      div_le_div_of_nonneg_right (hc_anti ξ m hξm.le) h2.le
    have hmB : m - ξ < c m / (2 * k ξ₁) := by simp only [B] at hBξ; linarith
    have : 2 * k ξ₁ < c m / (m - ξ) := by
      rw [lt_div_iff₀ h2]
      rw [lt_div_iff₀ (by linarith)] at hmB
      linarith
    linarith
  -- minimum on [A, B]
  have hAB : Set.Icc A B ⊆ Set.Iio m := fun x hx => lt_of_le_of_lt hx.2 hBm
  obtain ⟨ξs, hξsAB, hmin⟩ := (isCompact_Icc (a := A) (b := B)).exists_isMinOn
    ⟨ξ₁, hAξ₁, hξ₁B.le⟩ (hk_cont.mono hAB)
  have hglob : ∀ η, η < m → k ξs ≤ k η := by
    intro η hη
    have hs1 : k ξs ≤ k ξ₁ := hmin ⟨hAξ₁, hξ₁B.le⟩
    rcases lt_or_ge η A with h | h
    · exact hs1.trans (hleft η h)
    rcases le_or_gt η B with h' | h'
    · exact hmin ⟨h, h'⟩
    · exact hs1.trans (hright η h' hη).le
  -- the minimiser set
  set S : Set ℝ := {ξ : ℝ | ξ < m ∧ ∀ η : ℝ, η < m → c ξ / (m - ξ) ≤ c η / (m - η)}
  have hSB : ∀ ξ ∈ S, ξ ≤ B := by
    rintro ξ ⟨hξm, hξmin⟩
    by_contra h; push_neg at h
    have := hξmin ξ₁ hξ₁m
    have := hright ξ h hξm
    simp only [k] at *
    linarith
  have hSeq : S = {ξ ∈ Set.Iic B | k ξ ≤ k ξs} := by
    ext ξ
    constructor
    · intro hξ
      exact ⟨hSB ξ hξ, hξ.2 ξs (hAB hξsAB)⟩
    · rintro ⟨hξB, hξle⟩
      refine ⟨lt_of_le_of_lt hξB hBm, fun η hη => ?_⟩
      exact hξle.trans (hglob η hη)
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact (hk_cont.mono (fun x (hx : x ≤ B) => lt_of_le_of_lt hx hBm)).preimage_isClosed_of_isClosed
      isClosed_Iic isClosed_Iic
  have hSne : S.Nonempty := ⟨ξs, hAB hξsAB, hglob⟩
  have hSbdd : BddAbove S := ⟨B, hSB⟩
  have hβ := hSclosed.csSup_mem hSne hSbdd
  refine ⟨sSup S, ⟨hβ, fun ξ hξ => le_csSup hSbdd hξ⟩, ?_⟩
  have hbdd : BddBelow (Set.range fun ξ : Set.Iio m => c ξ / (m - ξ)) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact (hk_pos i i.2).le⟩
  apply le_antisymm
  · exact ciInf_le hbdd ⟨sSup S, hβ.1⟩
  · have : Nonempty (Set.Iio m) := ⟨⟨m - 1, by simp⟩⟩
    exact le_ciInf (fun η => hβ.2 η η.2)
