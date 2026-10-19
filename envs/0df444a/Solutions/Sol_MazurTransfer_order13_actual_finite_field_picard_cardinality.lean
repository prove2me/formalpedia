-- Prove2me | solution 1 for MazurTransfer.order13_actual_finite_field_picard_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T07:32:48.759598+00:00
-- url     : https://prove2.me/submissions/282f2872-257e-4377-a49b-efa246447e6b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Generic divisor interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: close the unchanged existing F3/F5 arithmetic Picard
cardinality contract by specializing the accepted literal-curve theorem.
Named downstream consumer: the existing finite-field arithmetic Picard mission
and the rational Jacobian torsion reduction bound.
-/
import Theorems.Thm_MazurTransfer_order13_actual_picard_cardinality_three_or_five
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_MazurTransfer_Order13DegreeTwoClosedPoints
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_degree_two_closed_point_counts
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
open AlgebraicGeometry AlgebraicCurve CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 3) (by decide)).1
noncomputable local instance : Algebra (ZMod 3) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))).toAlgebra
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 5) (by decide)).1
noncomputable local instance : Algebra (ZMod 5) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))).toAlgebra

theorem solution :
    Nat.card (AlgebraicCurve.Pic0 (ZMod 3)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField) = 19 ∧
    Nat.card (AlgebraicCurve.Pic0 (ZMod 5)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField) = 19  := by
  exact ⟨(MazurTransfer.order13_actual_picard_cardinality_three_or_five 3 (Or.inl rfl)).2,
    (MazurTransfer.order13_actual_picard_cardinality_three_or_five 5 (Or.inr rfl)).2⟩

#print axioms solution
