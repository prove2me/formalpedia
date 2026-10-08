-- Prove2me | solution 1 for MazurHuang.eq_one_of_curve_35a1_equation
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:23:50.193773+00:00
-- url     : https://prove2.me/submissions/b3597fd5-1210-43ff-8d7a-9bb8e637bfa0

/-
Rational points of the elliptic curve 35a1: z^2 + z = w^3 + w^2 + 9w + 1 forces w = 1.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (the predicate OnE35)
  * FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (n35_threeIsogenyX_ne_zero and its inputs, E35_three_torsion_x_zero, E35_affine_w_eq_one; the
    vanishing of 3P is assembled from the two published descent theorems)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35
import Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_eq_three_nsmul
import Theorems.Thm_MazurHuang_threeIsogeny35_three_nsmul_eq_three_pow_nsmul
import Theorems.Thm_MazurHuang_threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean and FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open MazurHuang.ThreeIsogeny35

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 61-62
def OnE35 (w z : ℚ) : Prop :=
  z ^ 2 + z = w ^ 3 + w ^ 2 + 9 * w + 1

/-- The explicit dual isogeny composed with the explicit three-isogeny is multiplication by three
(statement as in `FLT/Assumptions/MazurProof/RationalPointsX135.lean`), here the published theorem
`MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul`. -/
theorem dual_comp_threeIsogenyPoint (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P :=
  MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul P

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 9-45
def n35TripleDen (x : ℚ) : ℚ :=
  x * (3 * x + 28) * (x ^ 2 + 12 * x + 336)

def n35TripleXNum (x : ℚ) : ℚ :=
  x ^ 9 - 2688 * x ^ 7 - 103936 * x ^ 6 - 1204224 * x ^ 5 -
    4214784 * x ^ 4 + 119418880 * x ^ 3 + 1888223232 * x ^ 2 +
    13217562624 * x + 30840979456

def n35TripleYNum (x y : ℚ) : ℚ :=
  y * (x ^ 3 - 448 * x - 6272) *
    (x ^ 3 + 28 * x ^ 2 - 112 * x + 3136) *
    (x ^ 6 + 36 * x ^ 5 + 4480 * x ^ 4 + 82880 * x ^ 3 +
      878080 * x ^ 2 + 4566016 * x + 9834496)

private theorem n35TripleDen_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : n35TripleDen x ≠ 0 := by
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hlin
    have hxval : x = -28 / 3 := by linarith
    rw [hxval] at h
    norm_num [OnE35Short] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero (mul_ne_zero hx hlin) hquad

private theorem threeIsogenyX_eq_den (x : ℚ) (hx : x ≠ 0) :
    threeIsogenyX x = 3 * n35TripleDen x / x ^ 3 := by
  unfold threeIsogenyX n35TripleDen
  field_simp [hx]
  ring

private theorem threeIsogenyY_eq_factor (x y : ℚ) (hx : x ≠ 0) :
    threeIsogenyY x y = 27 * y * (x ^ 3 - 448 * x - 6272) / x ^ 3 := by
  unfold threeIsogenyY
  field_simp [hx]
  ring

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 334-339
private theorem n35_threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : threeIsogenyX x ≠ 0 := by
  rw [threeIsogenyX_eq_den x hx]
  exact div_ne_zero
    (mul_ne_zero (by norm_num) (n35TripleDen_ne_zero hx h))
    (pow_ne_zero 3 hx)

/-- Weak three-descent and three-adic separatedness annihilate every rational point after
multiplication by three (statement as in `FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean`),
here assembled from the published theorems
`MazurHuang.threeIsogeny35_three_nsmul_eq_three_pow_nsmul` and
`MazurHuang.threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible`. -/
theorem E35_three_nsmul_eq_zero (P : E35ShortPoint) : 3 • P = 0 :=
  MazurHuang.threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible P
    (fun n => MazurHuang.threeIsogeny35_three_nsmul_eq_three_pow_nsmul P n)

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 1237-1273
theorem E35_three_torsion_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hthree :
      3 • (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) = 0) :
    x = 0 := by
  by_contra hx
  have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
  have hphi := n35_threeIsogenyX_ne_zero hx hcurve
  have hnonzero :
      dualThreeIsogenyPoint
          (threeIsogenyPoint
            (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint)) ≠ 0 := by
    rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
    unfold WeierstrassCurve.Affine.Point.mk
    rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
    apply WeierstrassCurve.Affine.Point.some_ne_zero
  apply hnonzero
  rw [dual_comp_threeIsogenyPoint]
  exact hthree

/-- The only affine rational points on the conductor-35 quotient have
first coordinate one. -/
theorem E35_affine_w_eq_one {w z : ℚ} (hE : OnE35 w z) : w = 1 := by
  let x : ℚ := 4 * (w - 1)
  let y : ℚ := 8 * z + 4
  have hshort : OnE35Short x y := by
    unfold OnE35Short x y
    unfold OnE35 at hE
    linear_combination 64 * hE
  have hns : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E35ShortCurve_equation_iff x y).mpr hshort)
  have hthree := E35_three_nsmul_eq_zero
    (WeierstrassCurve.Affine.Point.some x y hns : E35ShortPoint)
  have hx := E35_three_torsion_x_zero hns hthree
  dsimp [x] at hx
  linarith


end

end MazurProof.RationalPointsX135

end

theorem solution
    {w z : ℚ}
    (h : z ^ 2 + z = w ^ 3 + w ^ 2 + 9 * w + 1) :
    w = 1 :=
  MazurProof.RationalPointsX135.E35_affine_w_eq_one h
