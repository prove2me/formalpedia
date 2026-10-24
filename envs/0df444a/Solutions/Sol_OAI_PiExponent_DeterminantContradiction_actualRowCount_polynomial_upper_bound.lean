-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:50:17.979643+00:00
-- url     : https://prove2.me/submissions/8689d277-53a0-4dd8-a983-88fd400cf26e

import Mathlib
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open OAI.PiExponent

namespace PXRC

lemma factor_le (u H : ℝ) (hH : 0 ≤ H) :
    ((⌊H / u⌋₊ + 1 : ℕ) : ℝ) ≤ (|u|⁻¹ + 1) * (H + 1) := by
  push_cast
  rcases lt_or_ge 0 u with hu | hu
  · have h1 : (⌊H / u⌋₊ : ℝ) ≤ H / u := Nat.floor_le (div_nonneg hH hu.le)
    rw [abs_of_pos hu]
    have : H / u ≤ (H + 1) * u⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hu.le)
    nlinarith [inv_nonneg.2 hu.le]
  · have h0 : ⌊H / u⌋₊ = 0 := Nat.floor_eq_zero.2 (lt_of_le_of_lt (div_nonpos_of_nonneg_of_nonpos hH hu) one_pos)
    rw [h0]; push_cast
    nlinarith [abs_nonneg u, inv_nonneg.2 (abs_nonneg u)]

lemma card_le {n : ℕ} (u : Fin n → ℝ) (H : ℝ) (hH : 0 ≤ H) :
    ((strictWeightedSimplex u H).card : ℝ) ≤ (∏ i, (|u i|⁻¹ + 1)) * (H + 1) ^ n := by
  classical
  have h1 : (strictWeightedSimplex u H).card ≤ (realWeightedSimplex u H).card := by
    unfold strictWeightedSimplex; exact Finset.card_filter_le _ _
  have h2 : (realWeightedSimplex u H).card ≤ ∏ i, (⌊H / u i⌋₊ + 1) := by
    unfold realWeightedSimplex
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Fintype.card_piFinset]; simp
  have h3 : ((∏ i, (⌊H / u i⌋₊ + 1) : ℕ) : ℝ) ≤ ∏ i, ((|u i|⁻¹ + 1) * (H + 1)) := by
    push_cast
    exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => by
      have := factor_le (u i) H hH; push_cast at this; exact this)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
  calc ((strictWeightedSimplex u H).card : ℝ) ≤ ((∏ i, (⌊H / u i⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1.trans h2
    _ ≤ _ := h3

end PXRC

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) : ∃ C : Real, 0 < C ∧ ∀ H : Real, 1 ≤ H → (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1) := by
  set u := InterpolationMatrix.rowWeights d.v0 d.base.theta
    (MatrixArithmetic.logWeights (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) with hu
  refine ⟨(d.K + 1) * ∏ i, (|u i|⁻¹ + 1), by positivity, fun H hH => ?_⟩
  unfold OAI.PiExponent.DeterminantContradiction.actualRowCount
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  push_cast
  have hc := PXRC.card_le u H (by linarith)
  have hK : (d.K : ℝ) ≤ d.K + 1 := by linarith
  calc (d.K : ℝ) * ((strictWeightedSimplex u H).card : ℝ)
      ≤ (d.K + 1) * ((∏ i, (|u i|⁻¹ + 1)) * (H + 1) ^ (d.m + 1)) :=
        mul_le_mul hK hc (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring
