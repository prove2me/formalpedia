-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDiamondTrace.order_three_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T17:02:56.271134+00:00
-- url     : https://prove2.me/submissions/dcc60b11-b00c-4547-8e3e-6db959d2b74b

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

namespace MazurTransfer.Order13DiamondTraceSquarePublicHelpers20261017
theorem diamond_square_order : orderOf (diamondAlgEquiv ^ 2) = 3 := by
  rw [orderOf_pow' (x := diamondAlgEquiv) (n := 2) (by decide), diamondAlgEquiv_order]
  norm_num

end MazurTransfer.Order13DiamondTraceSquarePublicHelpers20261017

theorem solution (c : ActualPicard) :
    c + (rho ^ 2) c + (rho ^ 4) c = 0 := by
  let e : RatFunc ℚ ≃ₐ[ℚ] IntermediateField.fixedField
      (Subgroup.zpowers (diamondAlgEquiv ^ 2)) :=
    Order13ActualOrderThreeFixedField.rationalQuotientFieldEquiv.trans
      (IntermediateField.equivOfEq
        Order13ActualOrderThreeFixedField.actual_order_three_fixed_field)
  have hfinite : IsOfFinOrder (diamondAlgEquiv ^ 2) := by
    exact orderOf_pos_iff.mp (by rw [MazurTransfer.Order13DiamondTraceSquarePublicHelpers20261017.diamond_square_order]; decide)
  have h := cyclic_pic0_trace_eq_zero (diamondAlgEquiv ^ 2) hfinite e c
  rw [MazurTransfer.Order13DiamondTraceSquarePublicHelpers20261017.diamond_square_order] at h
  simpa [Fin.sum_univ_succ, pow_succ, rho_pow_apply, rho_apply, mul_smul, add_assoc] using h


#print axioms solution
