-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m01
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:15:02.955422+00:00
-- url     : https://prove2.me/submissions/7bc45638-9095-4eab-9e8b-8ab3f648214f

import Mathlib
import Definitions.Def_NahmiasPerishable_Inventory_Cycles

set_option autoImplicit false

open NahmiasPerishable.Inventory

theorem solution (K h rate life : ℝ) (hK : 0 < K) (hh : 0 < h)
    (hrate : 0 < rate) (hlife : 0 < life) :
    let Q := min (Real.sqrt (2*K*rate/h)) (rate*life)
    0 < Q ∧ (∀ R, 0 < R → fixedCycleCost K h rate life Q ≤ fixedCycleCost K h rate life R) ∧
      pos (Q-rate*life) = 0 := by
  intro Q
  have hQdef : Q = min (Real.sqrt (2*K*rate/h)) (rate*life) := rfl
  have hQs : 0 < Real.sqrt (2*K*rate/h) := Real.sqrt_pos.mpr (by positivity)
  have hlm : 0 < rate * life := mul_pos hrate hlife
  have hQpos : 0 < Q := by rw [hQdef]; exact lt_min hQs hlm
  have hQle : Q ≤ rate * life := by rw [hQdef]; exact min_le_right _ _
  -- `h Q² ≤ 2Kλ`, with equality when the shelf-life constraint is slack.
  have hQsq : h * Q ^ 2 ≤ 2 * K * rate := by
    have h1 : Q ≤ Real.sqrt (2*K*rate/h) := by rw [hQdef]; exact min_le_left _ _
    have h2 : Q ^ 2 ≤ 2*K*rate/h :=
      calc Q ^ 2 ≤ (Real.sqrt (2*K*rate/h)) ^ 2 := pow_le_pow_left₀ hQpos.le h1 2
        _ = 2*K*rate/h := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ hh] at h2
    linarith
  have hQeq : Q < rate * life → h * Q ^ 2 = 2 * K * rate := by
    intro hlt
    have hQ' : Q = Real.sqrt (2*K*rate/h) := by
      rcases min_choice (Real.sqrt (2*K*rate/h)) (rate*life) with h' | h'
      · exact hQdef.trans h'
      · exact absurd (hQdef.trans h') (ne_of_lt hlt)
    rw [hQ', Real.sq_sqrt (by positivity)]
    field_simp
  -- The cycle cost below and above the expiry threshold `λ m`.
  have hc1 : ∀ R, 0 < R → R ≤ rate * life →
      fixedCycleCost K h rate life R = K * rate / R + h * R / 2 := by
    intro R hR hRle
    have hτ : cycleDuration rate life R = R / rate :=
      min_eq_left (by rw [div_le_iff₀ hrate]; linarith)
    unfold fixedCycleCost
    rw [hτ]
    field_simp
    ring
  have hc2 : ∀ R, rate * life ≤ R →
      fixedCycleCost K h rate life R = K / life + h * (R - rate * life / 2) := by
    intro R hR
    have hτ : cycleDuration rate life R = life :=
      min_eq_right (by rw [le_div_iff₀ hrate]; linarith)
    unfold fixedCycleCost
    rw [hτ]
  -- On `(0, λ m]` the EOQ cost `Kλ/R + hR/2` is minimised at `Q`.
  have key : ∀ R, 0 < R → R ≤ rate * life →
      fixedCycleCost K h rate life Q ≤ fixedCycleCost K h rate life R := by
    intro R hR hRle
    rw [hc1 Q hQpos hQle, hc1 R hR hRle]
    have hdiff : K * rate / R + h * R / 2 - (K * rate / Q + h * Q / 2)
        = (R - Q) * (h * R * Q - 2 * K * rate) / (2 * R * Q) := by
      field_simp
      ring
    have hnum : 0 ≤ (R - Q) * (h * R * Q - 2 * K * rate) := by
      rcases le_or_gt R Q with hRQ | hRQ
      · have h1 : h * R * Q ≤ h * Q * Q := by
          have := mul_le_mul_of_nonneg_left hRQ (mul_nonneg hh.le hQpos.le)
          nlinarith
        have h2 : h * R * Q - 2 * K * rate ≤ 0 := by nlinarith
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) h2
      · have hlt : Q < rate * life := lt_of_lt_of_le hRQ hRle
        have heq := hQeq hlt
        have h1 : h * Q * Q ≤ h * R * Q := by
          have := mul_le_mul_of_nonneg_left hRQ.le (mul_nonneg hh.le hQpos.le)
          nlinarith
        have h2 : 0 ≤ h * R * Q - 2 * K * rate := by nlinarith
        exact mul_nonneg (by linarith) h2
    have : 0 ≤ (R - Q) * (h * R * Q - 2 * K * rate) / (2 * R * Q) :=
      div_nonneg hnum (by positivity)
    linarith
  refine ⟨hQpos, fun R hR => ?_, ?_⟩
  · rcases le_or_gt R (rate * life) with hRle | hRgt
    · exact key R hR hRle
    · calc fixedCycleCost K h rate life Q ≤ fixedCycleCost K h rate life (rate * life) :=
            key _ hlm le_rfl
        _ ≤ fixedCycleCost K h rate life R := by
            rw [hc2 _ le_rfl, hc2 _ hRgt.le]
            nlinarith
  · unfold pos
    exact max_eq_right (by linarith)
