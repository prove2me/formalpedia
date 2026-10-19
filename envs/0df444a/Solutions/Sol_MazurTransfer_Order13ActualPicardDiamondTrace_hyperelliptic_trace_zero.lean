-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDiamondTrace.hyperelliptic_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T17:02:26.67997+00:00
-- url     : https://prove2.me/submissions/8a3accc8-5a32-4e15-89c2-a1997fc47dd8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original complete literal diamond Pic0 trace contract and proof retained.
Only public fixed-field, arithmetic endomorphism and cyclic-trace inputs are
imported. The curve-over-field instance is the explicit projection of the
accepted public actual function-field invariants statement.
Design boundary: actual arithmetic diamond-square/cube trace identities.
Named downstream consumer: original cyclotomic relation and nineteen norm.
Official Anthropic FLT trace interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualHyperellipticFixedFieldData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_RationalFixedFieldPicardTrace_cyclic_pic0_trace_eq_zero
noncomputable section
open MazurTransfer
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualConicFieldCubicExtension Order13ActualHyperellipticFixedField
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondExactOrder
open Order13ActualDiamondPicardEndomorphisms RationalFixedFieldPicardTrace
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance (B : IntermediateField ℚ (actualCurveFunctionField ℚ)) : Algebra ℚ B :=
  IntermediateField.algebra' B
local instance : Algebra ℚ conicField := IntermediateField.algebra' conicField
local instance : Algebra ℚ xField := IntermediateField.algebra' xField
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : IsCurveOver ℚ (actualCurveFunctionField ℚ) :=
  (MazurTransfer.order13_actual_function_field_invariants ℚ Fact.out).1

namespace MazurTransfer.Order13DiamondTraceCubePublicHelpers20261017
theorem diamond_cube_order : orderOf (diamondAlgEquiv ^ 3) = 2 := by
  rw [orderOf_pow' (x := diamondAlgEquiv) (n := 3) (by decide), diamondAlgEquiv_order]
  norm_num

end MazurTransfer.Order13DiamondTraceCubePublicHelpers20261017

theorem solution (c : ActualPicard) : c + (rho ^ 3) c = 0 := by
  let e : RatFunc ℚ ≃ₐ[ℚ] IntermediateField.fixedField
      (Subgroup.zpowers (diamondAlgEquiv ^ 3)) :=
    rationalInvolutionFieldEquiv.trans
      (IntermediateField.equivOfEq actual_hyperelliptic_fixed_field)
  have hfinite : IsOfFinOrder (diamondAlgEquiv ^ 3) := by
    exact orderOf_pos_iff.mp (by rw [MazurTransfer.Order13DiamondTraceCubePublicHelpers20261017.diamond_cube_order]; decide)
  have h := cyclic_pic0_trace_eq_zero (diamondAlgEquiv ^ 3) hfinite e c
  rw [MazurTransfer.Order13DiamondTraceCubePublicHelpers20261017.diamond_cube_order] at h
  simpa [Fin.sum_univ_succ, pow_succ, rho_pow_apply, rho_apply, mul_smul] using h

#print axioms solution
