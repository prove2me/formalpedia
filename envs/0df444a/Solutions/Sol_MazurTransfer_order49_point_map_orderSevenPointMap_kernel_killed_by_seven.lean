-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:27:11.783462+00:00
-- url     : https://prove2.me/submissions/42b18e20-f77b-4592-9911-1ec8514f3146

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenFamily_discriminant
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero

open Polynomial
theorem MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenFamily_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSevenFamily_discriminant <;> assumption
namespace MazurTransfer.Order49PointMapHelpers
/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/




section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

























namespace Point







lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl



variable [DecidableEq F]











end Point

end WeierstrassCurve.Affine

end

end MazurTransfer.Order49PointMapHelpers

namespace MazurTransfer.Order49PointMapHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert



























/-- The marked point `P = (0,0)` doubles to `(b,bc)` on Tate normal form. -/
theorem two_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  have hneg : W.toAffine.negY 0 0 = b := by
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.negY]
  have hnotvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    rw [hneg]
    exact fun h => hb h.symm
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hnotvertical]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
  have hx :
      W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = b := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
  have hy :
      W.toAffine.addY 0 0 0 (W.toAffine.slope 0 0 0 0) = b * c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₂ : W.toAffine.Nonsingular b (b * c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h00 h00
        (fun hxy => hnotvertical hxy.right)
    rwa [hx, hy] at h
  refine ⟨h₂, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnotvertical]
  exact MazurTransfer.Order49PointMapHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- The marked point `P = (0,0)` triples to `(c,b-c)` on Tate normal form. -/
theorem three_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  obtain ⟨h₂, hdouble⟩ := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope b 0 (b * c) 0 = c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    field_simp
    ring
  have hx :
      W.toAffine.addX b 0 (W.toAffine.slope b 0 (b * c) 0) = c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
    ring
  have hy :
      W.toAffine.addY b 0 (b * c) (W.toAffine.slope b 0 (b * c) 0) =
        b - c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₃ : W.toAffine.Nonsingular c (b - c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₂ h00
        (fun hxy => hb hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₃, ?_⟩
  rw [hdouble]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  exact MazurTransfer.Order49PointMapHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
  refine ⟨h₃, ?_⟩
  rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  exact htriple

/-- If also `c ≠ 0`, then `4P` has the displayed rational coordinates. -/
theorem four_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₄ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular
        (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope c 0 (b - c) 0 = (b - c) / c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    ring
  have hx :
      W.toAffine.addX c 0 (W.toAffine.slope c 0 (b - c) 0) =
        b * (b - c) / c ^ 2 := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
    field_simp [hc]
    ring
  have hy :
      W.toAffine.addY c 0 (b - c) (W.toAffine.slope c 0 (b - c) 0) =
        b ^ 2 * (c ^ 2 + c - b) / c ^ 3 := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring
  have h₄ : W.toAffine.Nonsingular
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₃ h00
        (fun hxy => hc hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₄, ?_⟩
  rw [htriple]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  exact MazurTransfer.Order49PointMapHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end MazurTransfer.Order49PointMapHelpers

namespace MazurTransfer.Order49PointMapHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert










































































/-- The marked origin is nonsingular on every nonsingular member of the
order-seven family. -/
theorem orderSevenOrigin_nonsingular
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular 0 0 := by
  apply (MazurTorsion.Kubert.orderSevenFamily d).toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.tateNormalCurve]

/-- The marked order-seven point `(0,0)` on the source family. -/
@[expose] public noncomputable def orderSevenOrigin
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
  .some 0 0 (MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenOrigin_nonsingular d)

/-- Nonsingularity excludes the three bad parameters of the order-seven
family. -/
theorem orderSevenFamily_parameters_ne
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  have hsource :
      d ^ 7 * (d - 1) ^ 7 *
          (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ≠ 0 := by
    simpa only [MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenFamily_Δ] using
      (MazurTorsion.Kubert.orderSevenFamily d).isUnit_Δ.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    apply hsource
    simp [hd]
  · intro hd
    apply hsource
    simp [hd]
  · intro hK
    apply hsource
    simp [hK]



private theorem orderSevenB_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenB d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  rw [show MazurTorsion.Kubert.orderSevenB d = d ^ 2 * (d - 1) by
    simp only [MazurTorsion.Kubert.orderSevenB]
    ring]
  exact mul_ne_zero (pow_ne_zero 2 hd0) (sub_ne_zero.mpr hd1)

private theorem orderSevenC_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenC d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  rw [show MazurTorsion.Kubert.orderSevenC d = d * (d - 1) by
    simp only [MazurTorsion.Kubert.orderSevenC]
    ring]
  exact mul_ne_zero hd0 (sub_ne_zero.mpr hd1)

/-- The marked origin is killed by seven on the parametrized family. -/
@[simp]
theorem seven_nsmul_orderSevenOrigin
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenOrigin d = 0 := by
  let b := MazurTorsion.Kubert.orderSevenB d
  let c := MazurTorsion.Kubert.orderSevenC d
  let h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0 := by
    simpa only [MazurTorsion.Kubert.orderSevenFamily, b, c] using
      MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  let P : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  change (7 : ℕ) • P = 0
  have hb : b ≠ 0 := by simpa only [b] using MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have hc : c ≠ 0 := by simpa only [c] using MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenC_ne_zero d
  have hrel : b ^ 2 - b * c - c ^ 3 = 0 := by
    simp only [b, c, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
    ring
  obtain ⟨h₃, hthree⟩ :=
    MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00
  obtain ⟨h₄, hfour⟩ :=
    MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.four_mul_origin_coordinates b c hb hc h00
  have hx₄ : b * (b - c) / c ^ 2 = c := by
    field_simp [hc]
    linear_combination hrel
  have hy₄ : b ^ 2 * (c ^ 2 + c - b) / c ^ 3 = c ^ 2 := by
    field_simp [hc]
    linear_combination (-b + c ^ 2) * hrel
  have hfour' :
      (4 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [show (4 : ℕ) • P = P + P + P + P by abel]
    simpa only [P] using hfour
  have hthree' :
      (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
    simpa only [P] using hthree
  have hfour_neg : (4 : ℕ) • P = -((3 : ℕ) • P) := by
    rw [hfour', hthree', WeierstrassCurve.Affine.Point.neg_some]
    exact MazurTransfer.Order49PointMapHelpers.WeierstrassCurve.Affine.Point.some_eq_some
      (MazurTorsion.Kubert.tateNormalCurve b c) hx₄ (by
        rw [hy₄]
        simp only [WeierstrassCurve.Affine.negY, MazurTorsion.Kubert.tateNormalCurve]
        ring)
  calc
    (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by abel
    _ = 0 := by rw [hfour_neg]; exact neg_add_cancel _













/-- Evaluation of the total point map away from the kernel poles. -/
theorem orderSevenPointMap_some_of_not_kernelX
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  simp [MazurTorsion.Kubert.orderSevenPointMap, hx]

/-- An affine point maps to infinity exactly at one of the three kernel
abscissae. -/
theorem orderSevenPointMap_some_eq_zero_iff
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  by_cases hx : MazurTorsion.Kubert.OrderSevenKernelX d x
  · simp [MazurTorsion.Kubert.orderSevenPointMap, hx]
  · rw [MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
    exact ⟨fun h ↦ (WeierstrassCurve.Affine.Point.some_ne_zero _ h).elim,
      fun h ↦ (hx h).elim⟩



private theorem seven_nsmul_of_kernelX
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : MazurTorsion.Kubert.OrderSevenKernelX d x) :
    (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 0 := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenOrigin d
  have hb : MazurTorsion.Kubert.orderSevenB d ≠ 0 := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have h00 := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  obtain ⟨h₂, htwo⟩ :=
    MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.two_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  obtain ⟨h₃, hthree⟩ :=
    MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.three_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  have hseven : (7 : ℕ) • P = 0 := MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
  have hmultiple (n : ℕ) : (7 : ℕ) • (n • P) = 0 := by
    calc
      (7 : ℕ) • (n • P) = n • ((7 : ℕ) • P) := by
        simp only [← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [hseven]; simp
  have hnegative {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
      (hQ : (7 : ℕ) • Q = 0) : (7 : ℕ) • (-Q) = 0 := by
    rw [neg_nsmul, hQ, neg_zero]
  rcases hx with hx0 | hxb | hxc
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some 0 0 h00 ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some 0 0 h00) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hx0
    rcases hxiff with h | h
    · rw [h]
      exact hseven
    · rw [h]
      exact hnegative hseven
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) h₂ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) h₂) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hxb
    rcases hxiff with h | h
    · rw [h, ← htwo]
      exact hmultiple 2
    · rw [h, ← htwo]
      exact hnegative (hmultiple 2)
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) h₃ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) h₃) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hxc
    rcases hxiff with h | h
    · rw [h, ← hthree]
      exact hmultiple 3
    · rw [h, ← hthree]
      exact hnegative (hmultiple 3)











/-- Every point in the zero fiber of the explicit Vélu function is killed
by seven. -/
theorem orderSevenPointMap_kernel_killed_by_seven
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  cases P with
  | zero => exact nsmul_zero 7
  | some x y h =>
      exact MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.seven_nsmul_of_kernelX h
        ((MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff h).mp hP)













end MazurTorsion.Kubert

end MazurTransfer.Order49PointMapHelpers

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  apply MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven <;> assumption
#print axioms solution
