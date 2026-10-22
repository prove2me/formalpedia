-- Prove2me | solution 1 for MarketplaceLeakage.Communication.piL_deriv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:44:06.758974+00:00
-- url     : https://prove2.me/submissions/51a892cb-68ed-400f-a6db-f06fed80b377

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

set_option autoImplicit false

open MarketplaceLeakage.Communication

theorem hasDeriv_PiL (v c q : ℝ) (η : ℝ) (hη : η < 1) :
    HasDerivAt (PiL v c q)
      (-((1 - q) * q * v / (1 - η) ^ 2) * ((2 - η) * q * η + 2 * (1 - η) ^ 2) + c * (1 - q)) η := by
  have hne : (1 - η) ≠ 0 := by linarith
  have hA : HasDerivAt (fun η : ℝ => 1 - η + η * q) (-1 + q) η := by
    have := ((hasDerivAt_id η).const_sub 1).add ((hasDerivAt_id η).mul_const q)
    exact this.congr_deriv (by ring)
  have hN : HasDerivAt (fun η : ℝ => (1 - (2 - q) * η) * q * v) (-(2 - q) * q * v) η := by
    have := (((hasDerivAt_id η).const_mul (2 - q)).const_sub 1).mul_const q |>.mul_const v
    simpa using this
  have hD : HasDerivAt (fun η : ℝ => 1 - η) (-1) η := by
    simpa using (hasDerivAt_id η).const_sub 1
  have hB : HasDerivAt (fun η : ℝ => (1 - (2 - q) * η) * q * v / (1 - η) - c)
      (((-(2 - q) * q * v) * (1 - η) - ((1 - (2 - q) * η) * q * v) * (-1)) / (1 - η) ^ 2) η := by
    have := (hN.div hD hne).sub_const c
    exact this
  have hP := hA.mul hB
  unfold PiL
  refine hP.congr_deriv ?_
  field_simp
  ring

theorem solution (v c : ℝ) (hvc : c < v) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ η : ℝ, η < 1 →
      HasDerivAt (PiL v c q)
        (-((1 - q) * q * v / (1 - η) ^ 2) * ((2 - η) * q * η + 2 * (1 - η) ^ 2) + c * (1 - q)) η) ∧
    (0 < v → c < q * v → StrictAntiOn (PiL v c q) (Set.Ico 0 1)) := by
  refine ⟨fun η hη => hasDeriv_PiL v c q η hη, fun hv hcq => ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro η hη
    exact (hasDeriv_PiL v c q η hη.2).continuousAt.continuousWithinAt
  · intro η hη
    rw [interior_Ico] at hη
    rw [(hasDeriv_PiL v c q η hη.2).deriv]
    have hD : 0 < (1 - η) ^ 2 := by have : 0 < 1 - η := by linarith [hη.2]
                                    positivity
    have h1q : 0 < 1 - q := by linarith
    have hqv : 0 < (1 - q) * q * v := by positivity
    have hK : 2 * (1 - η) ^ 2 ≤ (2 - η) * q * η + 2 * (1 - η) ^ 2 := by
      have : 0 ≤ (2 - η) * q * η := by
        have h2 : 0 ≤ 2 - η := by linarith [hη.2]
        have h3 : 0 ≤ η := hη.1.le
        positivity
      linarith
    have hKD : 2 ≤ ((2 - η) * q * η + 2 * (1 - η) ^ 2) / (1 - η) ^ 2 := by
      rw [le_div_iff₀ hD]; exact hK
    have e : -((1 - q) * q * v / (1 - η) ^ 2) * ((2 - η) * q * η + 2 * (1 - η) ^ 2)
        = -((1 - q) * q * v) * (((2 - η) * q * η + 2 * (1 - η) ^ 2) / (1 - η) ^ 2) := by
      field_simp
    rw [e]
    have h2 : (1 - q) * q * v * 2 ≤ (1 - q) * q * v * (((2 - η) * q * η + 2 * (1 - η) ^ 2) / (1 - η) ^ 2) :=
      mul_le_mul_of_nonneg_left hKD hqv.le
    have h3 : c * (1 - q) < q * v * (1 - q) := mul_lt_mul_of_pos_right hcq h1q
    nlinarith
