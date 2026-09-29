-- Prove2me | solution 1 for ModularCurve.eq_zero_of_mem_ssJSet_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7b9ee44e-aaf4-5530-8e71-9b827d8ab45f

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_three

open ModularCurve

set_option autoImplicit false

open ModularCurve WeierstrassCurve

namespace FltWs24
namespace SS

theorem two {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 2 k) (ha2 : a ^ (2 ^ 2) = a) : a = 0 := by
  by_contra h0
  have h2 : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  have h3 : a ^ 3 = 1 := by
    have h4 : a ^ 3 * a = 1 * a := by
      rw [← pow_succ, one_mul]; norm_num at ha2; exact ha2
    exact mul_right_cancel₀ h0 h4

  set W : WeierstrassCurve k := ⟨1, 0, 0, 0, a⁻¹⟩ with hW
  have hΔ : W.Δ = a⁻¹ := by
    simp only [hW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination (-a⁻¹ - 216 * (a⁻¹) ^ 2) * h2
  haveI hE : W.IsElliptic := ⟨by rw [hΔ]; exact isUnit_iff_ne_zero.mpr (inv_ne_zero h0)⟩
  have hc4 : W.c₄ = 1 := by
    simp only [hW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hj : W.j = a := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ, inv_inv, hc4]
    ring

  have heq : W.toAffine.Equation 0 a := by
    rw [WeierstrassCurve.Affine.equation_iff]
    show a ^ 2 + 1 * 0 * a + 0 * a = 0 ^ 3 + 0 * 0 ^ 2 + 0 * 0 + a⁻¹
    have : a ^ 2 = a⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc a ^ 2 * a = a ^ 3 := by ring
        _ = 1 := h3
    rw [this]; ring
  have hns : W.toAffine.Nonsingular 0 a := WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
  have h2P : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 a hns) = 0 := by
    rw [two_nsmul]
    refine WeierstrassCurve.Affine.Point.add_of_Y_eq rfl ?_
    show a = -a - W.a₁ * 0 - W.a₃
    simp only [hW]
    linear_combination a * h2
  have hP := ha W hj (WeierstrassCurve.Affine.Point.some 0 a hns) h2P
  exact absurd hP (by intro h; cases h)

theorem three {k : Type*} [Field k] [CharP k 3] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 3 k) (ha2 : a ^ (3 ^ 2) = a) : a = 0 := by
  by_contra h0
  have h3 : (3 : k) = 0 := by simpa using CharP.cast_eq_zero k 3
  have h8 : a ^ 8 = 1 := by
    have h9 : a ^ 8 * a = 1 * a := by
      rw [← pow_succ, one_mul]; norm_num at ha2; exact ha2
    exact mul_right_cancel₀ h0 h9

  set W : WeierstrassCurve k := ⟨0, 1, 0, 0, -a⁻¹⟩ with hW
  have hΔ : W.Δ = a⁻¹ := by
    simp only [hW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination (21 * a⁻¹ - 144 * (a⁻¹) ^ 2) * h3
  haveI hE : W.IsElliptic := ⟨by rw [hΔ]; exact isUnit_iff_ne_zero.mpr (inv_ne_zero h0)⟩
  have hc4 : W.c₄ = 1 := by
    simp only [hW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    linear_combination (5 : k) * h3
  have hj : W.j = a := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ, inv_inv, hc4]
    ring

  set x₀ : k := (a⁻¹) ^ 3 with hx₀
  have hx₀3 : x₀ ^ 3 = a⁻¹ := by
    rw [hx₀, ← pow_mul]
    show (a⁻¹) ^ 9 = a⁻¹
    rw [inv_pow, show (9 : ℕ) = 8 + 1 from rfl, pow_add, h8, one_mul, pow_one]
  have hx₀0 : x₀ ≠ 0 := by rw [hx₀]; exact pow_ne_zero _ (inv_ne_zero h0)
  have heq : W.toAffine.Equation x₀ x₀ := by
    rw [WeierstrassCurve.Affine.equation_iff]
    show x₀ ^ 2 + 0 * x₀ * x₀ + 0 * x₀ = x₀ ^ 3 + 1 * x₀ ^ 2 + 0 * x₀ + -a⁻¹
    rw [hx₀3]; ring
  have hns : W.toAffine.Nonsingular x₀ x₀ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
  have hnegY : W.toAffine.negY x₀ x₀ = -x₀ := by
    show -x₀ - W.a₁ * x₀ - W.a₃ = -x₀
    simp only [hW]; ring
  have hy : x₀ ≠ W.toAffine.negY x₀ x₀ := by
    rw [hnegY]
    intro h
    apply hx₀0

    linear_combination (-1 : k) * h + x₀ * h3
  have hslope : W.toAffine.slope x₀ x₀ x₀ x₀ = 1 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hnegY]
    show (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * x₀) / (x₀ - -x₀) = 1
    simp only [hW]
    rw [div_eq_one_iff_eq (by
      intro h; apply hx₀0; linear_combination (-1 : k) * h + x₀ * h3)]
    linear_combination (x₀ ^ 2) * h3
  have hX : W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ x₀ x₀) = x₀ := by
    rw [hslope]
    show (1 : k) ^ 2 + W.a₁ * 1 - W.a₂ - x₀ - x₀ = x₀
    simp only [hW]
    linear_combination (-x₀) * h3
  have hY : W.toAffine.addY x₀ x₀ x₀ (W.toAffine.slope x₀ x₀ x₀ x₀) = W.toAffine.negY x₀ x₀ := by
    rw [WeierstrassCurve.Affine.addY, hX, hnegY]
    show -(W.toAffine.negAddY x₀ x₀ x₀ (W.toAffine.slope x₀ x₀ x₀ x₀)) - W.a₁ * x₀ - W.a₃ = -x₀
    rw [WeierstrassCurve.Affine.negAddY, hX]
    simp only [hW]; ring
  have h3P : (3 : ℕ) • (WeierstrassCurve.Affine.Point.some x₀ x₀ hns) = 0 := by
    rw [succ_nsmul, two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    exact WeierstrassCurve.Affine.Point.add_of_Y_eq hX hY
  have hzero := ha W hj (WeierstrassCurve.Affine.Point.some x₀ x₀ hns) h3P
  exact absurd hzero (by intro h; cases h)

end FltWs24.SS

open ModularCurve in
theorem solution {k : Type*} [Field k] [CharP k 3] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 3 k) (ha2 : a ^ (3 ^ 2) = a) : a = 0 :=
  FltWs24.SS.three a ha ha2

end S_ModularCurve_eq_zero_of_mem_ssJSet_three
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_three (solution)
