-- Prove2me | solution 1 for NoHair.TwoCentre.optical_confinement
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:31:58.3678+00:00
-- url     : https://prove2.me/submissions/c22760dd-c45b-4b9f-ad47-6763982c189e

import Mathlib

open Set
open scoped RealInnerProductSpace

namespace NoHair.TwoCentre

private abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Integrate a speed bound by a time derivative on the segment. -/
private theorem travel_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x dx : ℝ → V} {τ dτ : ℝ → ℝ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt τ (dτ t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖dx t‖ ≤ dτ t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖x s - x 0‖ ≤ τ s - τ 0 := by
  let f t := x t - x 0
  let B t := τ t - τ 0
  have hf (t) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (dx t) t :=
    (hx t ht).sub_const _
  have hB (t) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt B (dτ t) t :=
    (hτ t ht).sub_const _
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [f, B]) (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hbound t (Ico_subset_Icc_self ht)) hs

private theorem inverse_distance_deriv {x : ℝ → Space} {dx b : Space} {t : ℝ}
    (hx : HasDerivAt x dx t) (hne : x t ≠ b) :
    HasDerivAt (fun s => 1 / ‖x s - b‖) (-⟪x t - b, dx⟫ / ‖x t - b‖ ^ 3) t := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hsq := ((hx.sub_const b).norm_sq).sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hsq
  have hh := (hasDerivAt_const t (1 : ℝ)).fun_div hsq hn
  convert! hh using 1
  field_simp [hn]
  ring

private theorem pole_bound {x dx : ℝ → Space} {τ dτ : ℝ → ℝ} {b : Space}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt τ (dτ t) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ b)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, (1 / ‖x t - b‖) ^ 2 * ‖dx t‖ ≤ dτ t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 / ‖x s - b‖ ≤ 1 / ‖x 0 - b‖ + (τ s - τ 0) := by
  have h := travel_bound (fun t ht => inverse_distance_deriv (hx t ht) (hreg t ht)) hτ
    (fun t ht => ?_) hs
  · have hle := le_abs_self (1 / ‖x s - b‖ - 1 / ‖x 0 - b‖)
    rw [Real.norm_eq_abs] at h
    linarith
  · have hn : 0 < ‖x t - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hreg t ht))
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hn 3)]
    refine le_trans ?_ (hbound t ht)
    rw [div_le_iff₀ (pow_pos hn 3)]
    calc
      _ ≤ ‖x t - b‖ * ‖dx t‖ := abs_real_inner_le_norm _ _
      _ = _ := by field_simp [hn.ne']

end NoHair.TwoCentre

open NoHair.TwoCentre

/-- On the two-centre exterior, finite coordinate time confines every optical
causal path to a compact set a positive distance from both poles. -/
theorem solution
    (b₁ b₂ x₀ : EuclideanSpace ℝ (Fin 3)) (h₁ : x₀ ≠ b₁) (h₂ : x₀ ≠ b₂)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K ∧ b₁ ∉ K ∧ b₂ ∉ K ∧
    ∀ (x dx : ℝ → EuclideanSpace ℝ (Fin 3)) (τ dτ : ℝ → ℝ),
      x 0 = x₀ →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t ∧ HasDerivAt τ (dτ t) t ∧
        x t ≠ b₁ ∧ x t ≠ b₂ ∧
        (1 + 1 / ‖x t - b₁‖ + 1 / ‖x t - b₂‖) ^ 2 * ‖dx t‖ ≤ dτ t) →
      ∀ s ∈ Icc (0 : ℝ) 1, τ s - τ 0 ≤ L → x s ∈ K := by
  let R (b : EuclideanSpace ℝ (Fin 3)) := 1 / (1 / ‖x₀ - b‖ + L)
  have hR (b) (hb : x₀ ≠ b) : 0 < R b := by
    have : 0 < ‖x₀ - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
    dsimp [R]
    positivity
  let K := (Metric.closedBall x₀ L ∩ {z | R b₁ ≤ ‖z - b₁‖}) ∩ {z | R b₂ ≤ ‖z - b₂‖}
  have hclosed (b) : IsClosed {z | R b ≤ ‖z - b‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  refine ⟨K, ((isCompact_closedBall x₀ L).inter_right (hclosed b₁)).inter_right (hclosed b₂),
    ?_, ?_, ?_⟩
  · intro h
    have hh : R b₁ ≤ ‖b₁ - b₁‖ := h.1.2
    simpa using (hR b₁ h₁).not_ge (by simpa using hh)
  · intro h
    have hh : R b₂ ≤ ‖b₂ - b₂‖ := h.2
    simpa using (hR b₂ h₂).not_ge (by simpa using hh)
  · intro x dx τ dτ hx₀ hpath s hs htime
    have hx t ht := (hpath t ht).1
    have hτ t ht := (hpath t ht).2.1
    let U t := 1 + 1 / ‖x t - b₁‖ + 1 / ‖x t - b₂‖
    have hspeed (t) (ht : t ∈ Icc (0 : ℝ) 1) (k : ℝ) (hk : 0 ≤ k) (hu : k ≤ U t) :
        k ^ 2 * ‖dx t‖ ≤ dτ t :=
      (mul_le_mul_of_nonneg_right (sq_le_sq' (by linarith) hu) (norm_nonneg _)).trans
        (hpath t ht).2.2.2.2
    have hu (t : ℝ) : 1 ≤ U t ∧ 1 / ‖x t - b₁‖ ≤ U t ∧ 1 / ‖x t - b₂‖ ≤ U t := by
      dsimp [U]
      have ha : 0 ≤ 1 / ‖x t - b₁‖ := by positivity
      have hb : 0 ≤ 1 / ‖x t - b₂‖ := by positivity
      exact ⟨by linarith, by linarith, by linarith⟩
    have hball := travel_bound hx hτ (fun t ht => by
      simpa using hspeed t ht 1 (by norm_num) (hu t).1) hs
    rw [hx₀] at hball
    have hradius (b) (hb : x₀ ≠ b) (hxreg : ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ b)
        (hUb : ∀ t, 1 / ‖x t - b‖ ≤ U t) : R b ≤ ‖x s - b‖ := by
      have hbnd := pole_bound hx hτ hxreg (fun t ht => hspeed t ht _ (by positivity) (hUb t)) hs
      rw [hx₀] at hbnd
      have hp : 0 < ‖x s - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hxreg s hs))
      have hinv : 1 / ‖x s - b‖ ≤ 1 / ‖x₀ - b‖ + L := by linarith
      have hp₀ : 0 < ‖x₀ - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
      apply (div_le_iff₀ (show 0 < 1 / ‖x₀ - b‖ + L by positivity)).2
      linarith [(div_le_iff₀ hp).1 hinv]
    exact ⟨⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hball.trans htime,
      hradius b₁ h₁ (fun t ht => (hpath t ht).2.2.1) (fun t => (hu t).2.1)⟩,
      hradius b₂ h₂ (fun t ht => (hpath t ht).2.2.2.1) (fun t => (hu t).2.2)⟩
