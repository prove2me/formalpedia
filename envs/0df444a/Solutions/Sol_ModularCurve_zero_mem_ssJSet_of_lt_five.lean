-- Prove2me | solution 1 for ModularCurve.zero_mem_ssJSet_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/21b1fdc2-1d0d-5725-a5cc-9a164069d937

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_zero_mem_ssJSet_of_lt_five

set_option autoImplicit false

open ModularCurve

namespace Ws14Port

theorem doubling_identity {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) :
    (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
      + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
      - (W.a₂ + 3 * x) * (y - W.toAffine.negY x y) ^ 2
      = -(3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x)) * h

theorem eq_zero_of_two_nsmul_eq_zero_of_char_two {K : Type*} [Field K] [DecidableEq K] [CharP K 2]
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : W.j = 0) (P : W.toAffine.Point)
    (hP : 2 • P = 0) : P = 0 := by
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have ha1 : W.a₁ = 0 := W.j_eq_zero_iff_of_char_two.mp hj
  rw [two_nsmul] at hP
  have hneg : P = -P := eq_neg_of_add_eq_zero_left hP
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  exfalso
  rw [WeierstrassCurve.Affine.Point.neg_some] at hneg
  injection hneg with _ hy
  have ha3 : W.a₃ = 0 := by
    simp only [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy - y * h2 - x * ha1
  apply W.Δ'.ne_zero
  rw [W.coe_Δ', W.Δ_of_char_two, ha1, ha3]
  ring

theorem eq_zero_of_three_nsmul_eq_zero_of_char_three {K : Type*} [Field K] [DecidableEq K]
    [CharP K 3] (W : WeierstrassCurve K) [W.IsElliptic] (hj : W.j = 0) (P : W.toAffine.Point)
    (hP : 3 • P = 0) : P = 0 := by
  have h3 : (3 : K) = 0 := by simpa using CharP.cast_eq_zero K 3
  have hb2 : W.b₂ = 0 := W.j_eq_zero_iff_of_char_three.mp hj
  have hΔ : W.Δ = W.b₄ ^ 3 := by
    rw [W.Δ_of_char_three, hb2]
    linear_combination (-3 * W.b₄ ^ 3) * h3
  have hb4 : W.b₄ ≠ 0 := fun h =>
    W.Δ'.ne_zero (by rw [W.coe_Δ', hΔ, h, zero_pow three_ne_zero])
  have hb8 : W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation_of_char_three, hb2, zero_mul, zero_sub]
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul] at hP
  have h2P : P + P = -P := eq_neg_of_add_eq_zero_left hP
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  exfalso
  by_cases hy : y = W.toAffine.negY x y
  ·
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy] at h2P
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.Affine.Point.neg_some] at h2P
    injection h2P with hX _
    have hd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
    set d := y - W.toAffine.negY x y with hd_def
    set n := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hn_def
    set ℓ := W.toAffine.slope x x y y with hℓ_def
    have hℓ : ℓ * d = n := by
      rw [hℓ_def, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      exact div_mul_cancel₀ _ hd
    simp only [WeierstrassCurve.Affine.addX] at hX

    have key : n ^ 2 + W.a₁ * n * d - (W.a₂ + 3 * x) * d ^ 2 = 0 := by
      linear_combination d ^ 2 * hX - (n + ℓ * d) * hℓ - W.a₁ * d * hℓ
    have ident := doubling_identity W hxy.1
    have hΨ : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0 := by
      linear_combination ident - key
    have hb4sq : W.b₄ ^ 2 = 0 := by
      linear_combination -hΨ + (x ^ 4 + W.b₄ * x ^ 2 + W.b₆ * x) * h3 + x ^ 3 * hb2 + hb8
    exact hb4 (pow_eq_zero_iff two_ne_zero |>.mp hb4sq)

end Ws14Port

theorem solution
    {q : ℕ} [Fact q.Prime] (hq : q < 5) {K : Type*} [Field K] [DecidableEq K] [CharP K q] :
    (0 : K) ∈ ssJSet q K := by
  have hp : q.Prime := Fact.out
  have hq23 : q = 2 ∨ q = 3 := by
    interval_cases q
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hp (by decide)
  intro W _ hj P hP
  rcases hq23 with rfl | rfl
  · exact Ws14Port.eq_zero_of_two_nsmul_eq_zero_of_char_two W hj P hP
  · exact Ws14Port.eq_zero_of_three_nsmul_eq_zero_of_char_three W hj P hP

end S_ModularCurve_zero_mem_ssJSet_of_lt_five
end P2MW
export P2MW.S_ModularCurve_zero_mem_ssJSet_of_lt_five (solution)
