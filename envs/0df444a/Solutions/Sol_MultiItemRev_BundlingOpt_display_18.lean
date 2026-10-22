-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.display_18
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:29.462292+00:00
-- url     : https://prove2.me/submissions/0b067a5f-fd9e-470a-a281-81bf276f22d2

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

theorem solution (M : Mechanism (Fin 2)) (hIC : IsIC M) (hsym : IsSymmetric M)
    (a y z : ℝ≥0) (hy : a ≤ y) (hz : a ≤ z) :
    buyerPayoff M ![y, z] ≤ buyerPayoff M ![y + z - a, a] := by
  have hbsw : ∀ x, buyerPayoff M (swap2 x) = buyerPayoff M x := by
    intro x
    have h1 := hsym x
    have h2 := hsym (swap2 x)
    have e : swap2 (swap2 x) = x := by
      funext i
      simp [swap2]
    rw [e] at h2
    have s0 : swap2 x 0 = x 1 := by simp [swap2]
    have s1 : swap2 x 1 = x 0 := by simp [swap2]
    unfold buyerPayoff
    rw [Fin.sum_univ_two, Fin.sum_univ_two, s0, s1, ← h1.1, h2.1, ← h1.2]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0, w = y + z - a := ⟨_, rfl⟩
  rw [← hw]
  have hwr : (w : ℝ) = (y : ℝ) + z - a := by
    rw [hw, NNReal.coe_sub (le_trans hy le_self_add), NNReal.coe_add]
  have hyr : (a : ℝ) ≤ y := by exact_mod_cast hy
  have hzr : (a : ℝ) ≤ z := by exact_mod_cast hz
  set t : ℝ := ((y : ℝ) - a) / (((y : ℝ) - a) + ((z : ℝ) - a)) with ht_def
  have ht : t * (((y : ℝ) - a) + ((z : ℝ) - a)) = (y : ℝ) - a := by
    by_cases h : ((y : ℝ) - a) + ((z : ℝ) - a) = 0
    · have : (y : ℝ) - a = 0 := by linarith
      rw [h, this]; ring
    · rw [ht_def]; field_simp
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  have ht1 : t ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have h1t : 0 ≤ 1 - t := by linarith
  have e0 : (y : ℝ) = t * w + (1 - t) * a := by
    rw [hwr]; linear_combination (-1 : ℝ) * ht
  have e1 : (z : ℝ) = t * a + (1 - t) * w := by
    rw [hwr]; linear_combination ht
  have hbX2 : buyerPayoff M ![a, w] = buyerPayoff M ![w, a] := by
    have := hbsw ![w, a]
    have e : swap2 ![w, a] = ![a, w] := by
      funext i
      fin_cases i <;> simp [swap2]
    rw [e] at this
    exact this
  have hA := hIC ![w, a] ![y, z]
  have hB := hIC ![a, w] ![y, z]
  rw [hbX2] at hB
  have hZ : buyerPayoff M ![y, z] =
      M.q ![y, z] 0 * (y : ℝ) + M.q ![y, z] 1 * (z : ℝ) - M.s ![y, z] := by
    simp only [buyerPayoff, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hA hB
  have hmix : M.q ![y, z] 0 * (y : ℝ) + M.q ![y, z] 1 * (z : ℝ) - M.s ![y, z] =
      t * (M.q ![y, z] 0 * (w : ℝ) + M.q ![y, z] 1 * (a : ℝ) - M.s ![y, z]) +
      (1 - t) * (M.q ![y, z] 0 * (a : ℝ) + M.q ![y, z] 1 * (w : ℝ) - M.s ![y, z]) := by
    rw [e0, e1]; ring
  rw [hZ, hmix]
  nlinarith [mul_le_mul_of_nonneg_left hA ht0, mul_le_mul_of_nonneg_left hB h1t]
