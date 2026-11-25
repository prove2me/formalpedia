-- Prove2me | solution 1 for GlobalTheory.IntBall.colGram_three_unitLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:05.720458+00:00
-- url     : https://prove2.me/submissions/ae1615e3-7b52-4704-9fe2-88e60f9f88d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall
namespace GlobalTheory.IntBall
theorem _root_.solution : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  intro M hd hu
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h01 : M 0 1 = 0 := hu 0 1 (by decide)
  have h02 : M 0 2 = 0 := hu 0 2 (by decide)
  have h12 : M 1 2 = 0 := hu 1 2 (by decide)
  have e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  have e2 : lminor (Mᴴ * M) 2 =
      (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0 := by
    unfold lminor
    exact Matrix.det_fin_two _
  have g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have g2 : lminor (Mᴴ * M) 2 =
      ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      <;> ring
  have pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · unfold colGram
    rw [g1, add_assoc, pos _ (by positivity), ← add_assoc]
  · unfold colGram
    rw [g2, add_assoc, pos _ (by positivity), ← add_assoc]
end GlobalTheory.IntBall
