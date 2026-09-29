-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3084560a-8692-5c18-ac3c-f0ead44cadc4

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

open ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) :
    A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 := by
  classical

  set a : AlgebraicClosure ℚ := ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) with ha
  by_cases ha0 : a = 0
  · rw [ha0, Valuation.map_zero]; exact zero_lt_one
  by_contra hlt

  have hle : A.valuation a ≤ 1 := A.valuation_le_one ⟨a, ϖ.2.1⟩
  have hone : A.valuation a = 1 := le_antisymm hle (not_lt.mp hlt)
  have hinvA : a⁻¹ ∈ A := by
    apply A.mem_of_valuation_le_one
    rw [Valuation.map_inv, hone, inv_one]
  have hinvK : a⁻¹ ∈ K := IntermediateField.inv_mem K ϖ.2.2
  let ω : ↥(NodeLocalized.coeffSubring A K) := ⟨a⁻¹, ⟨hinvA, hinvK⟩⟩
  have hmul : ϖ * ω = 1 := Subtype.ext (mul_inv_cancel₀ ha0)

  have hunit : IsUnit (R.nodeConst K w ϖ) :=
    IsUnit.of_mul_eq_one (R.nodeConst K w ω) (by rw [← map_mul, hmul, map_one])

  have hmem : R.nodeConst K w ϖ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]
    exact Ideal.subset_span (by simp)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span (solution)
