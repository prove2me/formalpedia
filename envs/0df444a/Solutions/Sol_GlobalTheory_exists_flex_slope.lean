-- Prove2me | solution 1 for GlobalTheory.exists_flex_slope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:31.777173+00:00
-- url     : https://prove2.me/submissions/5831ea86-e77a-4ccb-a81d-1d5154d96a89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
namespace GlobalTheory
theorem _root_.solution {x y : F} (h : W.toAffine.Nonsingular x y) (h3 : W.Ψ₃.eval x = 0) :
    ∃ l : F, l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ = 3 * x := by
  rw [nonsingular_iff', equation_iff'] at h
  obtain ⟨hE, hN⟩ := h
  simp only [Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat] at h3
  have hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    refine hN.elim (fun h => h ?_) (fun h => h h0)
    refine pow_eq_zero_iff (two_ne_zero) |>.mp ?_
    linear_combination -h3 - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hE
      - (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        - (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) * h0
  obtain ⟨l, hl⟩ : ∃ l : F,
      l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y :=
    ⟨_, div_mul_cancel₀ _ hη⟩
  refine ⟨l, hl, mul_left_cancel₀ (pow_ne_zero 2 hη) ?_⟩
  linear_combination -h3 - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hE
    + (l * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
      + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl
end GlobalTheory
