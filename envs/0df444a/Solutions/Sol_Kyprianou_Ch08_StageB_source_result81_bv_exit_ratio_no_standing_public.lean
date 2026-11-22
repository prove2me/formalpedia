-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_bv_exit_ratio_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:07:53.810471+00:00
-- url     : https://prove2.me/submissions/1f04f269-a37b-4b67-9cf9-649eb2d8c22f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound
import Theorems.Thm_AvramDividend_Classical_stopped_scale_identity_to_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_bv_stopped_scale_balance_no_standing_public

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (hBV : A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    AvramDividend.Classical.twoSidedExitExpectation A q a x =
      ENNReal.ofReal (W x / W a) := by
  have hWpos : 0 < W a := by
    let C0 : ℝ := |A.c| + A.σ ^ 2 / 2 +
      ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂A.ν
    let C : ℝ := |C0| + 1
    have hβ0 : 0 ≤ φ + 1 := by linarith
    have hψ : ∀ θ : ℝ, φ + 1 ≤ θ → q < A.ψ θ := by
      intro θ hθ
      have hφθ : φ < θ := by linarith
      have hθpos : 0 < θ := lt_trans hφ hφθ
      have hsec := levy_psi_positive_secant_monotone A φ θ hφ hφθ.le
      have hsecq : q / φ ≤ A.ψ θ / θ := by simpa [hroot] using hsec
      have hmul : (q / φ) * θ ≤ (A.ψ θ / θ) * θ :=
        mul_le_mul_of_nonneg_right hsecq hθpos.le
      have hcancel : (A.ψ θ / θ) * θ = A.ψ θ := by
        field_simp [ne_of_gt hθpos]
      have hupper : (q / φ) * θ ≤ A.ψ θ := by simpa [hcancel] using hmul
      have hlow : q < (q / φ) * θ := by
        field_simp [ne_of_gt hφ]
        nlinarith [mul_lt_mul_of_pos_left hφθ hq]
      exact hlow.trans_le hupper
    have hquad : ∀ θ : ℝ, φ + 1 ≤ θ →
        A.ψ θ - q ≤ C * (1 + θ ^ 2) := by
      intro θ hθ
      have hθ1 : 1 ≤ θ := by linarith [hφ, hθ]
      have hpsi_up := psi_quadratic_upper A θ hθ1
      have hle0 : A.ψ θ - q ≤ A.ψ θ := by linarith
      have hle1 : A.ψ θ - q ≤ C0 * θ ^ 2 := hle0.trans hpsi_up
      have hC0le : C0 ≤ C := by
        have hleabs : C0 ≤ |C0| := le_abs_self C0
        dsimp [C]
        linarith
      have hθsq : 0 ≤ θ ^ 2 := sq_nonneg θ
      have hle2 : C0 * θ ^ 2 ≤ C * θ ^ 2 :=
        mul_le_mul_of_nonneg_right hC0le hθsq
      have hCnonneg : 0 ≤ C := by
        dsimp [C]
        positivity
      have hle3 : C * θ ^ 2 ≤ C * (1 + θ ^ 2) := by nlinarith
      exact hle1.trans (hle2.trans hle3)
    exact scaleFunction_strict_pos_of_eventual_psi_bound
      A q W hW (φ + 1) C hβ0 hψ hquad a ha
  have hBal :=
    Kyprianou.Ch08.StageB.p2m81_bv_stopped_scale_balance_no_standing_public
      A q φ hq hφ hroot W hW hBV a x ha hx0 hxa
  exact stopped_scale_identity_to_ratio
    (twoSidedExitExpectation A q a x) (W x) (W a) hBal hWpos
