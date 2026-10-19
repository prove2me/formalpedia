-- Prove2me | solution 1 for MazurTransfer.Order13ActualFunctionFieldGenerators.intermediateField_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T16:19:56.585977+00:00
-- url     : https://prove2.me/submissions/01bd0486-264f-4cde-96e1-626c127fd9d3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original complete actual coordinate field-generation proof retained.
Design boundary: any intermediate field containing the literal ordinary
x and y coordinates is the actual rational scheme function field.
Named downstream consumer: actual conic cubic and hyperelliptic fixed fields.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryPolynomialTranscendence
noncomputable section
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13PellActualOrdinaryChart MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution (S : IntermediateField ℚ (actualCurveFunctionField ℚ))
    (hx : xImage ℚ ∈ S) (hy : yImage ℚ ∈ S) : S = ⊤ := by
  have hcoeff (p : Polynomial ℚ) : polynomialEmbedding p ∈ S := by
    change polynomialAlgHom p ∈ S
    rw [polynomialAlgHom_eq_aeval]
    exact (Algebra.adjoin_le (by simpa using hx) :
      Algebra.adjoin ℚ {xImage ℚ} ≤ S.toSubalgebra) (Polynomial.aeval_mem_adjoin_singleton ℚ (xImage ℚ) (p := p))
  have hcoordinate (a : CoordinateRing ℚ) :
      algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) a ∈ S := by
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      induction p using Polynomial.induction_on with
      | C c => exact hcoeff c
      | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
      | monomial n c ih =>
        rw [pow_succ, ← mul_assoc, map_mul, map_mul]
        exact S.mul_mem ih hy
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (CoordinateRing ℚ) z
  exact S.div_mem (hcoordinate a) (hcoordinate b)


#print axioms solution
