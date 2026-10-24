-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.actualRowCount_has_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:07:46.772052+00:00
-- url     : https://prove2.me/submissions/4c3774d3-7690-47b4-b28e-6088dd6dff00

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib

section

open Filter Topology OAI.PiExponent OAI.PiExponent.DeterminantContradiction

namespace PiL25

theorem PiL11rowcount (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  unfold actualRowCount
  apply Fintype.card_pos_iff.2
  refine ⟨⟨⟨0, d.K_pos⟩, ⟨0, ?_⟩⟩⟩
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  simp [hH, hH.le]



lemma factor_le (w H : ℝ) (hH : 0 ≤ H) :
    ((⌊H / w⌋₊ + 1 : ℕ) : ℝ) ≤ max 1 (1 / w) * (H + 1) := by
  push_cast
  rcases le_or_gt w 0 with hw | hw
  · have : H / w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hH hw
    rw [Nat.floor_eq_zero.2 (by linarith)]
    have := le_max_left 1 (1 / w)
    push_cast; nlinarith
  · have h1 : (⌊H / w⌋₊ : ℝ) ≤ H / w := Nat.floor_le (div_nonneg hH hw.le)
    have h2 := le_max_left 1 (1 / w)
    have h3 := le_max_right 1 (1 / w)
    have : H / w = (1 / w) * H := by ring
    nlinarith

theorem card_le {n : ℕ} (w : Fin n → ℝ) (H : ℝ) (hH : 0 ≤ H) :
    ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) ≤ (∏ i, max 1 (1 / w i)) * (H + 1) ^ n := by
  classical
  have hsub : OAI.PiExponent.strictWeightedSimplex w H ⊆
      Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1)) := by
    intro a ha
    simp only [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex, Finset.mem_filter] at ha
    exact ha.1.1
  have h1 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h1
  simp only [Finset.card_range] at h1
  calc ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) ≤ ((∏ i, (⌊H / w i⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∏ i, (((⌊H / w i⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; rfl
    _ ≤ ∏ i, (max 1 (1 / w i) * (H + 1)) := Finset.prod_le_prod (fun i _ => by positivity)
          (fun i _ => factor_le (w i) H hH)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem main {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop,
      0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧
      (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1) := by
  classical
  set w := InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
    (MatrixArithmetic.logWeights (finiteDenominators d))
  refine ⟨d.K * ∏ i, max 1 (1 / w i), ?_, ?_⟩
  · have := d.K_pos
    have : 0 < ∏ i, max 1 (1 / w i) := Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    refine ⟨by exact_mod_cast PiL11rowcount nu d H hH, ?_⟩
    unfold actualRowCount
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (card_le w H hH.le) (Nat.cast_nonneg _)

end PiL25

end

open OAI OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧ (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1) := by
  apply PiL25.main <;> assumption
