-- Prove2me | solution 1 for OAI.PiExponent.exists_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T12:11:33.597125+00:00
-- url     : https://prove2.me/submissions/370aa267-cd8c-4179-ae54-18f84961a1d3

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
import Theorems.Thm_OAI_PiExponent_exists_rational_parameters
import Mathlib


namespace OAI
namespace PiExponent

theorem exists_eta_preserving_exponent_gap
    (nu theta A : ℝ) (hnu : 2 < nu) (hA : 0 < A)
    (hgap : 1 - theta < nu * (A - theta)) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      0 < nu * (A * (1 - eta) - theta) - (1 - theta) := by
  let gap : ℝ := nu * (A - theta) - (1 - theta)
  have hgap_pos : 0 < gap := by dsimp [gap]; linarith
  have hnu_pos : 0 < nu := by linarith
  have hden_pos : 0 < 2 * nu * A := by positivity
  let eta : ℝ := min (1 / 2) (gap / (2 * nu * A))
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hgap_pos hden_pos)
  have heta_half : eta ≤ 1 / 2 := min_le_left _ _
  have heta_lt_one : eta < 1 := by linarith
  have heta_gap : eta ≤ gap / (2 * nu * A) := min_le_right _ _
  have hscaled : eta * (2 * nu * A) ≤ gap :=
    (le_div_iff₀ hden_pos).mp heta_gap
  refine ⟨eta, heta_pos, heta_lt_one, ?_⟩
  dsimp [gap] at hgap_pos hscaled
  nlinarith

end PiExponent
end OAI

open OAI OAI.PiExponent

theorem solution (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  obtain ⟨theta, A, B, C, htheta, hthetaA, hAB, hB, hgap, hC, hBinv, hBC, hCtheta⟩ :=
    exists_rational_parameters ν hν
  obtain ⟨eta, heta, heta1, hgapeta⟩ := exists_eta_preserving_exponent_gap
    ν theta A hν (lt_trans htheta hthetaA) hgap
  exact ⟨⟨theta, A, B, C, eta, htheta, hthetaA, hAB, hB, hgap, hC,
    hBinv, hBC, hCtheta, heta, heta1, hgapeta⟩⟩

#print axioms solution
