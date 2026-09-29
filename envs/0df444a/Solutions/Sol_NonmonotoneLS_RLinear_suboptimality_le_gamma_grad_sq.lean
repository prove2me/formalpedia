-- Prove2me | solution 1 for NonmonotoneLS.RLinear.suboptimality_le_gamma_grad_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:20:20.234476+00:00
-- url     : https://prove2.me/submissions/b54af355-9a71-489d-bc1c-744ae30b2e93

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter
open NonmonotoneLS.RLinear

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) :
    ∀ y, f y - f xstar ≤ γ * ‖gradient f y‖ ^ 2 := by
  intro y

  rcases hsc with ⟨hγ, hstrong⟩

  have hs := hstrong xstar y

  have hsub : xstar - y = -(y - xstar) := by
    abel

  rw [hsub] at hs
  simp only [inner_neg_right, norm_neg, one_div] at hs

  have hcs :
      ⟪gradient f y, y - xstar⟫_ℝ ≤ ‖gradient f y‖ * ‖y - xstar‖ :=
    real_inner_le_norm (gradient f y) (y - xstar)

  have h2γ : 0 < (2 : ℝ) * γ := by
    positivity

  have hyoung :
      2 * ‖gradient f y‖ * ‖y - xstar‖
        ≤ (2 * γ) * ‖gradient f y‖ ^ 2
            + (2 * γ)⁻¹ * ‖y - xstar‖ ^ 2 := by
    simpa only using
      (two_mul_le_add_mul_sq
        (a := ‖gradient f y‖)
        (b := ‖y - xstar‖)
        h2γ)

  have hcs2 :
      2 * ⟪gradient f y, y - xstar⟫_ℝ
        ≤ 2 * ‖gradient f y‖ * ‖y - xstar‖ := by
    nlinarith [hcs]

  have hinner :
      2 * ⟪gradient f y, y - xstar⟫_ℝ
        ≤ (2 * γ) * ‖gradient f y‖ ^ 2
            + (2 * γ)⁻¹ * ‖y - xstar‖ ^ 2 :=
    hcs2.trans hyoung

  have hquad :
      0 ≤ (2 * γ)⁻¹ * ‖y - xstar‖ ^ 2 := by
    exact mul_nonneg
      (inv_nonneg.mpr h2γ.le)
      (sq_nonneg ‖y - xstar‖)

  nlinarith [hs, hinner, hquad]
