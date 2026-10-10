-- Prove2me | solution 1 for MazurTransfer.order13_actual_picard_cardinality_three_or_five
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:25:01.362651+00:00
-- url     : https://prove2.me/submissions/e30ec8c1-13f4-487c-81af-1eacc3a7e51b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve and effective-divisor certificates: MazurTheorem WIP at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Generic function-field and divisor
interfaces reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0, with attribution retained.
Design boundary: exact arithmetic Picard cardinality of the literal curve,
parameterized by q in {3,5}, with finiteness as a conclusion.
Named downstream consumer: actual represented Picard point counts and
rational Jacobian torsion bounds through compatible good reduction.
No genus, curve model, or Picard cardinality is supplied as a hypothesis.
-/
import Mathlib.FieldTheory.Perfect
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
import Theorems.Thm_MazurTransfer_order13_actual_finite_field_effective_degree_two_divisor_counts
import Theorems.Thm_MazurTransfer_genus_two_picard_count_via_degree_two_divisors
import Mathlib.Tactic.Linarith

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    let h104 : (104 : ZMod q) ≠ 0 := by rcases hq with rfl | rfl <;> decide
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1
        (ZMod q) h104).1
    letI : Algebra (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField :=
      (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q))).toAlgebra
    Finite (AlgebraicCurve.Pic0 (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField) ∧
    Nat.card (AlgebraicCurve.Pic0 (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField) = 19 := by
  letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
  have h104 : (104 : ZMod q) ≠ 0 := by rcases hq with rfl | rfl <;> decide
  letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)) :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1
      (ZMod q) h104).1
  letI : Algebra (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField :=
    (AlgebraicCurve.baseToFunctionField
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q))).toAlgebra
  have hinvariants := MazurTransfer.order13_actual_function_field_invariants (ZMod q) h104
  letI : AlgebraicCurve.IsCurveOver (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField := hinvariants.1
  letI : Algebra.EssFiniteType (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField := hinvariants.2.1
  have heffective :
      Nat.card {D : AlgebraicCurve.Divisor (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField //
          (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 19 + q := by
    rcases hq with rfl | rfl
    · change Nat.card {D : AlgebraicCurve.Divisor (ZMod 3)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField //
          (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 22
      exact MazurTransfer.order13_actual_finite_field_effective_degree_two_divisor_counts.1
    · change Nat.card {D : AlgebraicCurve.Divisor (ZMod 5)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField //
          (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 24
      exact MazurTransfer.order13_actual_finite_field_effective_degree_two_divisor_counts.2
  letI : Finite {D : AlgebraicCurve.Divisor (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField //
        (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} :=
    Nat.finite_of_card_ne_zero (by rw [heffective]; omega)
  obtain ⟨hfinite, hcount⟩ := MazurTransfer.genus_two_picard_count_via_degree_two_divisors
    (ZMod q) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField
      hinvariants.2.2.1 hinvariants.2.2.2.1
  rw [heffective, Nat.card_zmod] at hcount
  exact ⟨hfinite, by omega⟩

#print axioms solution
