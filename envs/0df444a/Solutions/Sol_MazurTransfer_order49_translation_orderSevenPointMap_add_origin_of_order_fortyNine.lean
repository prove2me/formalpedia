-- Prove2me | solution 1 for MazurTransfer.order49_translation_orderSevenPointMap_add_origin_of_order_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:54:48.684357+00:00
-- url     : https://prove2.me/submissions/46ddaea7-d784-46ca-85cf-a75424429552

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedY
import Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
import Theorems.Thm_MazurTransfer_order49_marked_origin_seven_nsmul_orderSevenOrigin
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_of_not_kernelX
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero
theorem MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne <;> assumption

theorem MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX <;> assumption

theorem MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedY <;> assumption

theorem MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • MazurTorsion.Kubert.orderSevenOrigin d = 0 := by
  apply MazurTransfer.order49_marked_origin_seven_nsmul_orderSevenOrigin <;> assumption
namespace MazurTransfer.Order49OriginTranslationConsumers
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

end MazurTransfer.Order49OriginTranslationConsumers

namespace MazurTransfer.Order49OriginTranslationConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Velu

/-- The abscissa of an affine point, extended by zero at infinity. -/
noncomputable def pointXOrZero (W : WeierstrassCurve ℚ) :
    W.toAffine.Point → ℚ
  | 0 => 0
  | .some x _ _ => x

/-- The completed ordinate `2y + a₁x + a₃` of an affine point, extended
by zero at infinity. -/
noncomputable def pointCompletedYOrZero (W : WeierstrassCurve ℚ) :
    W.toAffine.Point → ℚ
  | 0 => 0
  | .some x y _ => 2 * y + W.a₁ * x + W.a₃



@[simp] theorem pointXOrZero_some
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Nonsingular x y) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero W (.some x y h) = x :=
  rfl

@[simp] theorem pointXOrZero_neg
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero W (-P) = MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero W P := by
  cases P with
  | zero => rfl
  | some x y h => simp [WeierstrassCurve.Affine.Point.neg_some]



@[simp] theorem pointCompletedYOrZero_some
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Nonsingular x y) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero W (.some x y h) =
      2 * y + W.a₁ * x + W.a₃ :=
  rfl

@[simp] theorem pointCompletedYOrZero_neg
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero W (-P) = -MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero W P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.negY]
      ring

/-- The paired abscissa correction contributed by `R = (r, s)` and `-R`. -/
def pairXCorrection (W : WeierstrassCurve ℚ) (x r s : ℚ) : ℚ :=
  (6 * r ^ 2 + W.b₂ * r + W.b₄) / (x - r) +
    (2 * s + W.a₁ * r + W.a₃) ^ 2 / (x - r) ^ 2

/-- The formal derivative in `x` of `pairXCorrection`. -/
def pairDifferentialCorrection
    (W : WeierstrassCurve ℚ) (x r s : ℚ) : ℚ :=
  -(6 * r ^ 2 + W.b₂ * r + W.b₄) / (x - r) ^ 2 -
    2 * (2 * s + W.a₁ * r + W.a₃) ^ 2 / (x - r) ^ 3

/-- Pairing `R` and `-R` in the chord law gives the standard paired
abscissa term in Vélu's formula. -/
theorem pointXOrZero_add_pair
    (W : WeierstrassCurve ℚ) {x y r s : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hR : W.toAffine.Nonsingular r s)
    (hxr : x ≠ r) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero W (.some x y hP + .some r s hR) +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero W (.some x y hP + -(.some r s hR)) - 2 * r =
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection W x r s := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxr,
    WeierstrassCurve.Affine.Point.add_of_X_ne hxr]
  simp only [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection]
  rw [W.toAffine.slope_of_X_ne hxr, W.toAffine.slope_of_X_ne hxr]
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY]
  have hPcurve := hP.1
  have hRcurve := hR.1
  rw [WeierstrassCurve.Affine.equation_iff] at hPcurve hRcurve
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [sub_ne_zero.mpr hxr]
  linear_combination 2 * hPcurve - 2 * hRcurve

/-- The paired completed-ordinate sum is the derivative correction times
the completed ordinate of the input point. -/
theorem pointCompletedYOrZero_add_pair
    (W : WeierstrassCurve ℚ) {x y r s : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hR : W.toAffine.Nonsingular r s)
    (hxr : x ≠ r) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero W (.some x y hP + .some r s hR) +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero W (.some x y hP + -(.some r s hR)) =
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection W x r s *
        (2 * y + W.a₁ * x + W.a₃) := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxr,
    WeierstrassCurve.Affine.Point.add_of_X_ne hxr]
  simp only [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection]
  rw [W.toAffine.slope_of_X_ne hxr, W.toAffine.slope_of_X_ne hxr]
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have hPcurve := hP.1
  have hRcurve := hR.1
  rw [WeierstrassCurve.Affine.equation_iff] at hPcurve hRcurve
  field_simp [sub_ne_zero.mpr hxr]
  linear_combination
    (-2 * (2 * y + W.a₁ * x + W.a₃)) * hPcurve +
      (2 * (2 * y + W.a₁ * x + W.a₃)) * hRcurve

end MazurTorsion.Velu

end
end MazurTransfer.Order49OriginTranslationConsumers

namespace MazurTransfer.Order49OriginTranslationConsumers
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
  exact MazurTransfer.Order49OriginTranslationConsumers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

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
  obtain ⟨h₂, hdouble⟩ := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00
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
  exact MazurTransfer.Order49OriginTranslationConsumers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
  refine ⟨h₃, ?_⟩
  rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  exact htriple




end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end MazurTransfer.Order49OriginTranslationConsumers

namespace MazurTransfer.Order49OriginTranslationConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert




















































private theorem orderSevenVeluX_eq_pairCorrections
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluX d x = x +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x 0 0 +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
        (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) := by
  simp only [MazurTorsion.Kubert.orderSevenVeluX, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection,
    MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.tateNormalCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring

private theorem orderSevenVeluDifferential_eq_pairCorrections
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x = 1 +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x 0 0 +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) +
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
        (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) := by
  simp only [MazurTorsion.Kubert.orderSevenVeluDifferential,
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection,
    MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.tateNormalCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring

private def sevenOrbitCorrection
    {A : Type*} [AddCommGroup A] (f : A → ℚ) (P T : A) : ℚ :=
  f P + f (P + T) + f (P + (2 : ℕ) • T) +
      f (P + (3 : ℕ) • T) + f (P + (4 : ℕ) • T) +
      f (P + (5 : ℕ) • T) + f (P + (6 : ℕ) • T) -
    (f T + f ((2 : ℕ) • T) + f ((3 : ℕ) • T) +
      f ((4 : ℕ) • T) + f ((5 : ℕ) • T) + f ((6 : ℕ) • T))

private theorem sevenOrbitCorrection_add
    {A : Type*} [AddCommGroup A] (f : A → ℚ) (P T : A)
    (hT : (7 : ℕ) • T = 0) :
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection f (P + T) T =
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection f P T := by
  have hshift (n : ℕ) :
      P + T + n • T = P + (n + 1) • T := by
    rw [add_nsmul]
    simp
    abel
  have hshiftOne : P + T + T = P + (2 : ℕ) • T := by
    simp only [two_nsmul]
    abel
  simp only [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection]
  rw [hshiftOne, hshift 2, hshift 3, hshift 4, hshift 5,
    hshift 6, hT, add_zero]
  ring























private theorem orderSevenB_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenB d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  rw [show MazurTorsion.Kubert.orderSevenB d = d ^ 2 * (d - 1) by
    simp only [MazurTorsion.Kubert.orderSevenB]
    ring]
  exact mul_ne_zero (pow_ne_zero 2 hd0) (sub_ne_zero.mpr hd1)







private theorem orderSevenVelu_orbitFormulas
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluX d x =
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
          (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero (MazurTorsion.Kubert.orderSevenFamily d))
          (WeierstrassCurve.Affine.Point.some x y hP)
          (MazurTorsion.Kubert.orderSevenOrigin d) ∧
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
          (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
            (MazurTorsion.Kubert.orderSevenFamily d).a₃) =
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
          (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero (MazurTorsion.Kubert.orderSevenFamily d))
          (WeierstrassCurve.Affine.Point.some x y hP)
          (MazurTorsion.Kubert.orderSevenOrigin d) := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let T : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTorsion.Kubert.orderSevenOrigin d
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
  have hb : MazurTorsion.Kubert.orderSevenB d ≠ 0 := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have h00 := MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  have hT0 : T = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    dsimp only [T, MazurTorsion.Kubert.orderSevenOrigin]
  obtain ⟨h₂, hT2raw⟩ :=
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.two_nsmul_origin_coordinates
      (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  obtain ⟨h₃, hT3raw⟩ :=
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.three_nsmul_origin_coordinates
      (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  let h₂' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular
      (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) := by
    simpa only [MazurTorsion.Kubert.orderSevenFamily] using h₂
  let h₃' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular
      (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) := by
    simpa only [MazurTorsion.Kubert.orderSevenFamily] using h₃
  have hT2 : (2 : ℕ) • T =
      WeierstrassCurve.Affine.Point.some
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) h₂' := by
    rw [hT0]
    exact hT2raw.trans (MazurTransfer.Order49OriginTranslationConsumers.WeierstrassCurve.Affine.Point.some_eq_some
      (MazurTorsion.Kubert.orderSevenFamily d) rfl rfl)
  have hT3 : (3 : ℕ) • T =
      WeierstrassCurve.Affine.Point.some
        (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) h₃' := by
    rw [hT0]
    exact hT3raw.trans (MazurTransfer.Order49OriginTranslationConsumers.WeierstrassCurve.Affine.Point.some_eq_some
      (MazurTorsion.Kubert.orderSevenFamily d) rfl rfl)
  have hT6 : (6 : ℕ) • T = -T := by
    calc
      (6 : ℕ) • T = (7 : ℕ) • T - T := by abel
      _ = -T := by rw [hT7]; simp
  have hT5 : (5 : ℕ) • T = -((2 : ℕ) • T) := by
    calc
      (5 : ℕ) • T = (7 : ℕ) • T - (2 : ℕ) • T := by abel
      _ = -((2 : ℕ) • T) := by rw [hT7]; simp
  have hT4 : (4 : ℕ) • T = -((3 : ℕ) • T) := by
    calc
      (4 : ℕ) • T = (7 : ℕ) • T - (3 : ℕ) • T := by abel
      _ = -((3 : ℕ) • T) := by rw [hT7]; simp
  have hpair0 := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h00 hx0
  have hpairB := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h₂' hxb
  have hpairC := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h₃' hxc
  have hpairZ0 := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h00 hx0
  have hpairZB := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h₂' hxb
  have hpairZC := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero_add_pair
    (MazurTorsion.Kubert.orderSevenFamily d) hP h₃' hxc
  constructor
  · rw [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVeluX_eq_pairCorrections hx0 hxb hxc]
    change x +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x 0 0 +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
          (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairXCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
          (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) =
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P T
    simp only [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection]
    rw [hT2, hT3, hT4, hT5, hT6, hT2, hT3]
    rw [hT0]
    simp only [P, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero_some, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero_neg]
    linear_combination -hpair0 - hpairB - hpairC
  · rw [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_pairCorrections hx0 hxb hxc]
    change (1 +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x 0 0 +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
          (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) +
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pairDifferentialCorrection (MazurTorsion.Kubert.orderSevenFamily d) x
          (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d)) *
          (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
            (MazurTorsion.Kubert.orderSevenFamily d).a₃) =
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
        (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P T
    simp only [MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection]
    rw [hT2, hT3, hT4, hT5, hT6, hT2, hT3]
    rw [hT0]
    simp only [P, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero_some,
      MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero_neg]
    linear_combination -hpairZ0 - hpairZB - hpairZC



/-- Away from the kernel poles, the explicit Vélu point is invariant under
translation by the marked order-seven point. -/
theorem orderSevenVeluPoint_add_origin
    {d x y x' y' : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hP' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x' y')
    (hadd :
      (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) + MazurTorsion.Kubert.orderSevenOrigin d =
        WeierstrassCurve.Affine.Point.some x' y' hP')
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d)
    (hx0' : x' ≠ 0) (hxb' : x' ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc' : x' ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluPoint hP' hx0' hxb' hxc' =
      MazurTorsion.Kubert.orderSevenVeluPoint hP hx0 hxb hxc := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let P' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x' y' hP'
  let T : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTorsion.Kubert.orderSevenOrigin d
  have hadd' : P + T = P' := by
    simpa only [P, P', T] using hadd
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
  have hform := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVelu_orbitFormulas hP hx0 hxb hxc
  have hform' := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVelu_orbitFormulas hP' hx0' hxb' hxc'
  have hx : MazurTorsion.Kubert.orderSevenVeluX d x' = MazurTorsion.Kubert.orderSevenVeluX d x := by
    calc
      MazurTorsion.Kubert.orderSevenVeluX d x' =
          MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
            (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P' T := by
        simpa only [P', T] using hform'.1
      _ = MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
          (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointXOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P T := by
        rw [← hadd']
        exact MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection_add _ P T hT7
      _ = MazurTorsion.Kubert.orderSevenVeluX d x := by
        simpa only [P, T] using hform.1.symm
  have hcompleted :
      2 * MazurTorsion.Kubert.orderSevenVeluY d x' y' +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x' +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
        2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₃ := by
    calc
      2 * MazurTorsion.Kubert.orderSevenVeluY d x' y' +
            (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x' +
            (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
          MazurTorsion.Kubert.orderSevenVeluDifferential d x' *
            (2 * y' + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x' +
              (MazurTorsion.Kubert.orderSevenFamily d).a₃) :=
        MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY d x' y'
      _ = MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
          (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P' T := by
        simpa only [P', T] using hform'.2
      _ = MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection
          (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Velu.pointCompletedYOrZero (MazurTorsion.Kubert.orderSevenFamily d)) P T := by
        rw [← hadd']
        exact MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.sevenOrbitCorrection_add _ P T hT7
      _ = MazurTorsion.Kubert.orderSevenVeluDifferential d x *
          (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
            (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
        simpa only [P, T] using hform.2.symm
      _ = 2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₃ :=
        (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY d x y).symm
  have hy : MazurTorsion.Kubert.orderSevenVeluY d x' y' = MazurTorsion.Kubert.orderSevenVeluY d x y := by
    linear_combination
      (1 / 2 : ℚ) * hcompleted -
        ((MazurTorsion.Kubert.orderSevenQuotient d).a₁ / 2) * hx
  simp only [MazurTorsion.Kubert.orderSevenVeluPoint]
  exact MazurTransfer.Order49OriginTranslationConsumers.WeierstrassCurve.Affine.Point.some_eq_some
    (MazurTorsion.Kubert.orderSevenQuotient d) hx hy











private theorem seven_nsmul_of_kernelX
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : MazurTorsion.Kubert.OrderSevenKernelX d x) :
    (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 0 := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTorsion.Kubert.orderSevenOrigin d
  have hb : MazurTorsion.Kubert.orderSevenB d ≠ 0 := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have h00 := MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  obtain ⟨h₂, htwo⟩ :=
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.two_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  obtain ⟨h₃, hthree⟩ :=
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.three_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  have hseven : (7 : ℕ) • P = 0 := MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
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

/-- On an affine point of exact order `49`, the total explicit point map is
invariant under translation by the marked order-seven point. -/
private theorem orderSevenPointMap_add_origin_of_order_fortyNine_affine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d
        ((WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) + MazurTorsion.Kubert.orderSevenOrigin d) =
      MazurTorsion.Kubert.orderSevenPointMap d
        (WeierstrassCurve.Affine.Point.some x y hP) := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let T : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTorsion.Kubert.orderSevenOrigin d
  have h7P : (7 : ℕ) • P ≠ 0 := by
    intro hzero
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← horder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hzero
    norm_num at hdvd
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
  have hsumne : P + T ≠ 0 := by
    intro hzero
    have hseven : (7 : ℕ) • (P + T) = 0 := by
      rw [hzero]
      simp
    rw [nsmul_add, hT7, add_zero] at hseven
    exact h7P hseven
  obtain ⟨x', y', hP', hadd⟩ :
      ∃ (x' y' : ℚ)
        (hP' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x' y'),
          P + T = WeierstrassCurve.Affine.Point.some x' y' hP' := by
    cases hsum : P + T with
    | zero => exact (hsumne hsum).elim
    | some x' y' hP' => exact ⟨x', y', hP', rfl⟩
  have hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
    intro hkernel
    exact h7P (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_of_kernelX hP hkernel)
  have h7P' :
      (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x' y' hP' :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) ≠ 0 := by
    intro hzero
    rw [← hadd, nsmul_add, hT7, add_zero] at hzero
    exact h7P hzero
  have hx' : ¬MazurTorsion.Kubert.OrderSevenKernelX d x' := by
    intro hkernel
    exact h7P' (MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.seven_nsmul_of_kernelX hP' hkernel)
  change MazurTorsion.Kubert.orderSevenPointMap d (P + T) = MazurTorsion.Kubert.orderSevenPointMap d P
  rw [hadd, MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP' hx',
    show P = WeierstrassCurve.Affine.Point.some x y hP by rfl,
    MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
  exact MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenVeluPoint_add_origin hP hP'
    (by simpa only [P, T] using hadd)
    (fun h ↦ hx (Or.inl h))
    (fun h ↦ hx (Or.inr (Or.inl h)))
    (fun h ↦ hx (Or.inr (Or.inr h)))
    (fun h ↦ hx' (Or.inl h))
    (fun h ↦ hx' (Or.inr (Or.inl h)))
    (fun h ↦ hx' (Or.inr (Or.inr h)))



/-- Translation invariance at exact order `49`, stated for an arbitrary
source point. -/
theorem orderSevenPointMap_add_origin_of_order_fortyNine
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d (Q + MazurTorsion.Kubert.orderSevenOrigin d) =
      MazurTorsion.Kubert.orderSevenPointMap d Q := by
  cases Q with
  | zero =>
      have hfalse : (1 : ℕ) = 49 := by
        rw [← hQ]
        exact (addOrderOf_zero
          (G := (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      exact MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenPointMap_add_origin_of_order_fortyNine_affine
        hP hQ



















end MazurTorsion.Kubert

end MazurTransfer.Order49OriginTranslationConsumers

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d (Q + MazurTorsion.Kubert.orderSevenOrigin d) =
      MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.Order49OriginTranslationConsumers.MazurTorsion.Kubert.orderSevenPointMap_add_origin_of_order_fortyNine <;> assumption
#print axioms solution
