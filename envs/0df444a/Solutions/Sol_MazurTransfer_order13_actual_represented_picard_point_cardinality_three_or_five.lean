-- Prove2me | solution 1 for MazurTransfer.order13_actual_represented_picard_point_cardinality_three_or_five
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:54:14.455621+00:00
-- url     : https://prove2.me/submissions/b59fd71c-0a3d-4f53-a10c-a3857a281f11

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Picard/divisor interfaces reuse official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: actual represented Picard field-valued points have order 19
over F3 and F5, with finiteness as a conclusion and every rational base section
included. Named downstream consumer: compatible good reduction and rational
Jacobian torsion bounds for the unchanged order-13 obstruction.
Both the full actual group correspondence and actual arithmetic cardinality
are accepted public dependencies. No rank or point-cardinality is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_picard_group_equivalence
import Theorems.Thm_MazurTransfer_order13_actual_picard_cardinality_three_or_five

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem solution
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)),
      ∃ (D : RelativePic0Designation (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
        (h : RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε
          (algEquivZeroCut
            (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε) D),
        Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) ∧
        Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) = 19 ∧
        Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) ∧
        Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) = 19 := by
  letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
  have h104 : (104 : ZMod q) ≠ 0 := by rcases hq with rfl | rfl <;> decide
  letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)) :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1
      (ZMod q) h104).1
  letI : Algebra (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField :=
    (baseToFunctionField
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q))).toAlgebra
  intro ε
  obtain ⟨D, h, ⟨e⟩⟩ :=
    MazurTransfer.order13_actual_arithmetic_picard_group_equivalence (ZMod q) h104 ε
  let hG : RepresentsRelSubPic
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε
      (algEquivZeroGroupCut
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε).toSubPicCondition D := h
  letI := hG.grpObj
  have hcard := MazurTransfer.order13_actual_picard_cardinality_three_or_five q hq
  letI : Finite (Pic0 (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField) := hcard.1
  have hfinite : Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) :=
    Finite.of_injective e e.injective
  have hcount : Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) = 19 :=
    (Nat.card_congr e.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hcard.2)
  let pointEquiv :
      (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) ≃
        SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase :=
    { toFun := fun f => ⟨f.left, by simpa only [Over.mk_left, Over.mk_hom] using Over.w f⟩
      invFun := fun f => Over.homMk f.1 f.2
      left_inv := by intro f; apply Over.OverMorphism.ext; rfl
      right_inv := by intro f; apply Subtype.ext; rfl }
  letI := hfinite
  exact ⟨D, h, hfinite, hcount, Finite.of_surjective pointEquiv pointEquiv.surjective,
    (Nat.card_congr pointEquiv).symm.trans hcount⟩

#print axioms solution
