-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:25:36.717024+00:00
-- url     : https://prove2.me/submissions/dcb19262-5a04-40b5-af61-8eb78ff49b50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_row_card_pos
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_denominator_clear_v2
import Theorems.Thm_OAI_PiExponent_Arithmetic_gaussianInt_log_norm_lower_bound

open scoped BigOperators

theorem solution
    {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 θ q H) -
      (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
        OAI.PiExponent.Arithmetic.lcmConstant *
          (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin) ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  let N : ℝ := (Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
    (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H
  let E : ℝ := OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
    OAI.PiExponent.Arithmetic.lcmConstant *
      (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin
  have hcard := OAI.PiExponent.MatrixArithmetic.selectedMinor_row_card_pos
    (q := q) hq hK hv0 hθ hH
  have hN : 0 < N := by dsimp [N]; exact mul_pos hcard hH
  obtain ⟨D, hD, g, hg, hbound⟩ :=
    OAI.PiExponent.MatrixArithmetic.selectedMinor_denominator_clear_v2
      p q hq hK hw0 hv0 hθ hF hH hmin hwmin selection hdet
  have hlog := OAI.PiExponent.Arithmetic.gaussianInt_log_norm_lower_bound
    hD hdet g hg
  have hraw : -N * ((1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 θ q H) + E) ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det‖ := by
    dsimp [N, E] at hbound ⊢
    linarith
  rw [le_div_iff₀ hN]
  dsimp [N, E]
  nlinarith [hraw]