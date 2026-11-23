-- Prove2me | solution 1 for GlobalTheory.three_nsmul_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:48.50689+00:00
-- url     : https://prove2.me/submissions/5e300f3d-70ed-4354-ba00-4093fa105069

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_exists_flex_slope

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
theorem _root_.solution [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y) :
    3 • Point.some x y h = 0 ↔ W.Ψ₃.eval x = 0 := by
  rw [three'_nsmul]
  constructor
  · intro h0
    obtain ⟨l, n, e, -, -, s₁, s₂, s₃⟩ := exists_line_of_add_add_eq_zero h0
    simp only [Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
    have h2 : W.a₂ = l ^ 2 + W.a₁ * l - 3 * x := by linear_combination s₁
    have h4 : W.a₄ = 3 * x ^ 2 + 2 * l * n + W.a₁ * n + W.a₃ * l := by linear_combination -s₂
    have h6 : W.a₆ = n ^ 2 + W.a₃ * n - x ^ 3 := by linear_combination s₃
    rw [h2, h4, h6]
    ring
  · intro h3
    obtain ⟨l, h₁, h₂⟩ := exists_flex_slope h h3
    exact add_add_eq_zero_of_line h h h l (y - l * x) (by ring) (by ring) (by ring)
      (by linear_combination -h₂) (by linear_combination h₁ - 2 * x * h₂)
end GlobalTheory
