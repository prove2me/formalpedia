-- Prove2me | solution 1 for ICOTheory.Signaling.proposition_6_signaling_advantage_intervals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T13:23:39.638915+00:00
-- url     : https://prove2.me/submissions/9800cfa3-a5bd-4926-a201-b69f37f54080

import Mathlib
import Definitions.Def_ICOTheory_Signaling_SignalingAdvantage

set_option autoImplicit false

namespace ICOTheory.Signaling.P27a6

open ICOTheory.Signaling

/-- `y ≤ α*` iff `2 y d ≤ (1 - y)^2 s` with `d = 4 μH - 4 μL`, `s = σ^2 γ`. -/
theorem le_alphaStar_iff {μH μL σ γ y : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ)
    (hy0 : 0 < y) (hy1 : y < 1) :
    y ≤ alphaStar μH μL σ γ ↔ 2 * y * (4 * μH - 4 * μL) ≤ (1 - y) ^ 2 * (σ ^ 2 * γ) := by
  have hs : 0 < σ ^ 2 * γ := by positivity
  have hd : 0 < 4 * μH - 4 * μL := by linarith
  have hA : alphaStar μH μL σ γ =
      ((4 * μH - 4 * μL) + σ ^ 2 * γ -
        Real.sqrt ((4 * μH - 4 * μL) * ((4 * μH - 4 * μL) + 2 * (σ ^ 2 * γ)))) / (σ ^ 2 * γ) := by
    unfold alphaStar
    rw [show 2 * σ ^ 2 * γ = 2 * (σ ^ 2 * γ) by ring]
  rw [hA]
  generalize 4 * μH - 4 * μL = d at hd ⊢
  generalize σ ^ 2 * γ = s at hs ⊢
  rw [le_div_iff₀ hs]
  have hD0 : 0 ≤ d * (d + 2 * s) := by positivity
  have hR : 0 ≤ d + (1 - y) * s := by nlinarith
  constructor
  · intro h
    have h1 : Real.sqrt (d * (d + 2 * s)) ≤ d + (1 - y) * s := by linarith
    have h2 : d * (d + 2 * s) ≤ (d + (1 - y) * s) ^ 2 := by
      nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg (d * (d + 2 * s))]
    have h3 : s * (2 * y * d) ≤ s * ((1 - y) ^ 2 * s) := by nlinarith
    exact le_of_mul_le_mul_left h3 hs
  · intro h
    have h2 : d * (d + 2 * s) ≤ (d + (1 - y) * s) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h hs.le
      nlinarith
    have h1 : Real.sqrt (d * (d + 2 * s)) ≤ d + (1 - y) * s := by
      calc Real.sqrt (d * (d + 2 * s)) ≤ Real.sqrt ((d + (1 - y) * s) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = d + (1 - y) * s := Real.sqrt_sq hR
    linarith

theorem adv_iff {μH μL σ γ I C : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ)
    (ha0 : 0 < alphaBarT I μH) (ha1 : alphaBarT I μH < 1)
    (hb0 : 0 < alphaBarE I C μH) (hb1 : alphaBarE I C μH < 1) :
    SignalingAdvantage μH μL σ γ I C ↔
      (2 * alphaBarT I μH * (4 * μH - 4 * μL) ≤ (1 - alphaBarT I μH) ^ 2 * (σ ^ 2 * γ) ∧
        (1 - alphaBarE I C μH) ^ 2 * (σ ^ 2 * γ) < 2 * alphaBarE I C μH * (4 * μH - 4 * μL)) := by
  unfold SignalingAdvantage
  rw [le_alphaStar_iff hμ hσ hγ ha0 ha1, ← not_le, le_alphaStar_iff hμ hσ hγ hb0 hb1, not_le]

theorem crucial {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (hlt : a < b) :
    a * (1 - b) ^ 2 < b * (1 - a) ^ 2 := by
  have e : b * (1 - a) ^ 2 - a * (1 - b) ^ 2 = (b - a) * (1 - a * b) := by ring
  have h1 : 0 < b - a := by linarith
  have h2 : 0 < 1 - a * b := by nlinarith
  have := mul_pos h1 h2
  linarith

theorem part1_abs {μH a b s : ℝ} (hs : 0 < s) (ha0 : 0 < a) (hb0 : 0 < b) (hb1 : b < 1)
    (hlt : a < b) :
    ∃ μl μu : ℝ, μl < μu ∧ ∀ μL : ℝ, μL < μH →
      ((2 * a * (4 * μH - 4 * μL) ≤ (1 - a) ^ 2 * s ∧ (1 - b) ^ 2 * s < 2 * b * (4 * μH - 4 * μL))
        ↔ μl ≤ μL ∧ μL < μu) := by
  refine ⟨μH - (1 - a) ^ 2 * s / (8 * a), μH - (1 - b) ^ 2 * s / (8 * b), ?_, ?_⟩
  · have hc := crucial ha0 hb1 hlt
    have h8 : (1 - b) ^ 2 * s / (8 * b) < (1 - a) ^ 2 * s / (8 * a) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have e : (1 - a) ^ 2 * s * (8 * b) - (1 - b) ^ 2 * s * (8 * a)
          = 8 * s * (b * (1 - a) ^ 2 - a * (1 - b) ^ 2) := by ring
      have : 0 < 8 * s * (b * (1 - a) ^ 2 - a * (1 - b) ^ 2) := by
        apply mul_pos (by positivity); linarith
      linarith
    linarith
  · intro μL _
    have e1 : μH - (1 - a) ^ 2 * s / (8 * a) ≤ μL ↔
        2 * a * (4 * μH - 4 * μL) ≤ (1 - a) ^ 2 * s := by
      rw [show μH - (1 - a) ^ 2 * s / (8 * a) ≤ μL ↔ μH - μL ≤ (1 - a) ^ 2 * s / (8 * a) by
        constructor <;> intro h <;> linarith, le_div_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    have e2 : μL < μH - (1 - b) ^ 2 * s / (8 * b) ↔
        (1 - b) ^ 2 * s < 2 * b * (4 * μH - 4 * μL) := by
      rw [show μL < μH - (1 - b) ^ 2 * s / (8 * b) ↔ (1 - b) ^ 2 * s / (8 * b) < μH - μL by
        constructor <;> intro h <;> linarith, div_lt_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    rw [e1, e2]

theorem part2_abs {d γ a b : ℝ} (hd : 0 < d) (hγ : 0 < γ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hlt : a < b) :
    ∃ σl σu : ℝ, σl < σu ∧ ∀ σ : ℝ, 0 < σ →
      ((2 * a * d ≤ (1 - a) ^ 2 * (σ ^ 2 * γ) ∧ (1 - b) ^ 2 * (σ ^ 2 * γ) < 2 * b * d)
        ↔ σl ≤ σ ∧ σ < σu) := by
  have ha1' : 0 < (1 - a) ^ 2 := by have : 0 < 1 - a := by linarith
                                    positivity
  have hb1' : 0 < (1 - b) ^ 2 := by have : 0 < 1 - b := by linarith
                                    positivity
  refine ⟨Real.sqrt (2 * a * d / ((1 - a) ^ 2 * γ)), Real.sqrt (2 * b * d / ((1 - b) ^ 2 * γ)),
    ?_, ?_⟩
  · apply Real.sqrt_lt_sqrt (by positivity)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hc := crucial ha0 hb1 hlt
    have e : 2 * b * d * ((1 - a) ^ 2 * γ) - 2 * a * d * ((1 - b) ^ 2 * γ)
        = 2 * d * γ * (b * (1 - a) ^ 2 - a * (1 - b) ^ 2) := by ring
    have : 0 < 2 * d * γ * (b * (1 - a) ^ 2 - a * (1 - b) ^ 2) := by
      apply mul_pos (by positivity); linarith
    linarith
  · intro σ hσ
    have hsq : Real.sqrt (σ ^ 2) = σ := Real.sqrt_sq hσ.le
    have e1 : Real.sqrt (2 * a * d / ((1 - a) ^ 2 * γ)) ≤ σ ↔
        2 * a * d ≤ (1 - a) ^ 2 * (σ ^ 2 * γ) := by
      conv_lhs => rw [← hsq]
      rw [Real.sqrt_le_sqrt_iff (by positivity), div_le_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    have e2 : σ < Real.sqrt (2 * b * d / ((1 - b) ^ 2 * γ)) ↔
        (1 - b) ^ 2 * (σ ^ 2 * γ) < 2 * b * d := by
      conv_lhs => rw [← hsq]
      rw [Real.sqrt_lt_sqrt_iff (by positivity), lt_div_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    rw [e1, e2]

theorem main {μH γ I C : ℝ}
    (hγ : 0 < γ) (hI : 0 < I) (hC : 0 ≤ C) (hfund : C + I < μH / 4) :
    (∀ σ : ℝ, 0 < σ → ∃ μl μu : ℝ, μl < μu ∧
        ∀ μL : ℝ, μL < μH → (SignalingAdvantage μH μL σ γ I C ↔ μl ≤ μL ∧ μL < μu)) ∧
    (∀ μL : ℝ, μL < μH → ∃ σl σu : ℝ, σl < σu ∧
        ∀ σ : ℝ, 0 < σ → (SignalingAdvantage μH μL σ γ I C ↔ σl ≤ σ ∧ σ < σu)) := by
  have hT : 0 < μH / 4 := by linarith
  have hEC : 0 < μH / 4 - C := by linarith
  have ha0 : 0 < alphaBarT I μH := by unfold alphaBarT; positivity
  have ha1 : alphaBarT I μH < 1 := by
    unfold alphaBarT; rw [div_lt_one hT]; linarith
  have hb0 : 0 < alphaBarE I C μH := by unfold alphaBarE; positivity
  have hb1 : alphaBarE I C μH < 1 := by
    unfold alphaBarE; rw [div_lt_one hEC]; linarith
  rcases hC.lt_or_eq with hC0 | hC0
  · have hlt : alphaBarT I μH < alphaBarE I C μH := by
      unfold alphaBarT alphaBarE
      exact div_lt_div_of_pos_left hI hEC (by linarith)
    refine ⟨fun σ hσ => ?_, fun μL hμL => ?_⟩
    · obtain ⟨μl, μu, h1, h2⟩ := part1_abs (μH := μH) (show 0 < σ ^ 2 * γ by positivity)
        ha0 hb0 hb1 hlt
      refine ⟨μl, μu, h1, fun μL hμL => ?_⟩
      rw [adv_iff hμL hσ hγ ha0 ha1 hb0 hb1]
      exact h2 μL hμL
    · obtain ⟨σl, σu, h1, h2⟩ := part2_abs (show 0 < 4 * μH - 4 * μL by linarith) hγ
        ha0 ha1 hb0 hb1 hlt
      refine ⟨σl, σu, h1, fun σ hσ => ?_⟩
      rw [adv_iff hμL hσ hγ ha0 ha1 hb0 hb1]
      exact h2 σ hσ
  · have heq : alphaBarE I C μH = alphaBarT I μH := by
      unfold alphaBarT alphaBarE; rw [← hC0, sub_zero]
    have hno : ∀ μL σ : ℝ, μL < μH → 0 < σ → ¬ SignalingAdvantage μH μL σ γ I C := by
      intro μL σ hμL hσ h
      rw [adv_iff hμL hσ hγ ha0 ha1 hb0 hb1, heq] at h
      linarith [h.1, h.2]
    refine ⟨fun σ hσ => ⟨μH, μH + 1, by linarith, fun μL hμL => ?_⟩,
      fun μL hμL => ⟨-2, -1, by norm_num, fun σ hσ => ?_⟩⟩
    · constructor
      · intro h; exact absurd h (hno μL σ hμL hσ)
      · intro h; linarith [h.1]
    · constructor
      · intro h; exact absurd h (hno μL σ hμL hσ)
      · intro h; linarith [h.2]

end ICOTheory.Signaling.P27a6

open ICOTheory.Signaling in
theorem solution {μH γ I C : ℝ}
    (hγ : 0 < γ) (hI : 0 < I) (hC : 0 ≤ C) (hfund : C + I < μH / 4) :
    (∀ σ : ℝ, 0 < σ → ∃ μl μu : ℝ, μl < μu ∧
        ∀ μL : ℝ, μL < μH → (SignalingAdvantage μH μL σ γ I C ↔ μl ≤ μL ∧ μL < μu)) ∧
    (∀ μL : ℝ, μL < μH → ∃ σl σu : ℝ, σl < σu ∧
        ∀ σ : ℝ, 0 < σ → (SignalingAdvantage μH μL σ γ I C ↔ σl ≤ σ ∧ σ < σu)) := by
  exact ICOTheory.Signaling.P27a6.main hγ hI hC hfund
