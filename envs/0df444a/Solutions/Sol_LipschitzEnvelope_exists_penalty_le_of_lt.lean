-- Prove2me | solution 1 for LipschitzEnvelope.exists_penalty_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:47.114538+00:00
-- url     : https://prove2.me/submissions/d1c56dcd-ccb5-458d-919d-eee22f716364

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting

-- carved verbatim out of submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 819-854

section
set_option autoImplicit false
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (C A r : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hr : L xhat < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)) ≤ (r : EReal) := by
  have hn : ∀ᶠ x in 𝓝 xhat, L x < (r : EReal) := husc r hr
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  let B := max 0 ((C-r)/δ)
  let lam := max 0 A+B
  have hB : 0 ≤ B := le_max_left _ _
  have hlam : 0 ≤ lam := add_nonneg (le_max_left _ _) hB
  refine ⟨lam,hlam,?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_cases hd : ‖x-xhat‖ < δ
  · have hl : L x ≤ (r : EReal) := (hlocal (by simpa [dist_eq_norm] using hd)).le
    have hp : (0 : EReal) ≤ ((lam*‖x-xhat‖ : ℝ) : EReal) := by
      exact EReal.coe_nonneg.mpr (mul_nonneg hlam (norm_nonneg _))
    exact le_trans (by simpa using EReal.sub_le_sub le_rfl hp) hl
  · have hdist : δ ≤ ‖x-xhat‖ := le_of_not_gt hd
    have hfrac : (C-r)/δ ≤ B := le_max_right _ _
    have hCd : C-r ≤ B*δ := (div_le_iff₀ hδ).mp hfrac
    have hBd : B*δ ≤ B*‖x-xhat‖ := mul_le_mul_of_nonneg_left hdist hB
    have hAd : A*‖x-xhat‖ ≤ max 0 A*‖x-xhat‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hb : C+A*‖x-xhat‖-lam*‖x-xhat‖ ≤ r := by
      dsimp [lam]
      nlinarith
    have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam*‖x-xhat‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    exact hh.trans (EReal.coe_le_coe_iff.mpr hb)

end
