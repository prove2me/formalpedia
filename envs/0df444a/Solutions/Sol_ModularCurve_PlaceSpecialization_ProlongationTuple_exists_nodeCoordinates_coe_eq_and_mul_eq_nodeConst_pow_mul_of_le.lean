-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/21139e35-8526-5e9c-8671-61a486225708

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace DATUMTRANSPORT

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N))
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')

include hKK' in
theorem fieldOver_mono : NodeLocalized.fieldOver (N * q) K ≤ NodeLocalized.fieldOver (N * q) K' := by
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  exact ⟨⟨z, hKK' hz⟩, rfl⟩

include hKK' in
theorem nodeIntegersOver_mono : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w :=
  fun _ hf => ⟨hf.1, fieldOver_mono (q := q) (N := N) hKK' hf.2⟩

include hKK' in

def incl : ↥(R.nodeIntegersOver K w) →+* ↥(R.nodeIntegersOver K' w) :=
  Subring.inclusion (nodeIntegersOver_mono R w hKK')

theorem coe_incl (f : ↥(R.nodeIntegersOver K w)) :
    ((incl R w hKK' f : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) = f :=
  Subring.coe_inclusion _ _

theorem mk_incl (f : ↥(R.nodeIntegersOver K w)) :
    (⟨(incl R w hKK' f : ↥(modularFunctionFieldBar (N * q))), (incl R w hKK' f).2.1⟩ : ↥(R.nodeIntegers w)) =
      ⟨f, f.2.1⟩ :=
  Subtype.ext (coe_incl R w hKK' f)

set_option maxHeartbeats 1600000 in

theorem incl_nodeConst (ϖ : ↥(NodeLocalized.coeffSubring A K)) (ϖK' : ↥(NodeLocalized.coeffSubring A K'))
    (h : (ϖ : AlgebraicClosure ℚ) = (ϖK' : AlgebraicClosure ℚ)) :
    incl R w hKK' (R.nodeConst K w ϖ) = R.nodeConst K' w ϖK' := by
  apply Subtype.ext
  rw [coe_incl, coe_nodeConst, coe_nodeConst, h]

variable [PerfectField k]

include hKK' in

def transport (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := incl R w hKK' c.x
  y := incl R w hKK' c.y
  x_fst := by rw [mk_incl]; exact c.x_fst
  x_snd := by rw [mk_incl]; exact c.x_snd
  y_snd := by rw [mk_incl]; exact c.y_snd
  y_fst := by rw [mk_incl]; exact c.y_fst

theorem transport_x (c : R.NodeCoordinates K w) : (transport R w hKK' c).x = incl R w hKK' c.x := rfl
theorem transport_y (c : R.NodeCoordinates K w) : (transport R w hKK' c).y = incl R w hKK' c.y := rfl

include hKK' in
set_option maxHeartbeats 1600000 in
theorem main (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K')) (r : ℕ) (u₀ : ↥(NodeLocalized.coeffSubring A K')) (hu₀ : IsUnit u₀)
    (hϖ : (ϖ : AlgebraicClosure ℚ) = ((ϖ' ^ r * u₀ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ)) :
    ∃ (c' : R.NodeCoordinates K' w) (uK' : ↥(R.nodeIntegersOver K' w)), IsUnit uK' ∧
      ((uK' : ↥(modularFunctionFieldBar (N * q))) = u) ∧
      ((c'.x : ↥(modularFunctionFieldBar (N * q))) = c.x) ∧ ((c'.y : ↥(modularFunctionFieldBar (N * q))) = c.y) ∧
      IsUnit (R.nodeConst K' w u₀ ^ E * uK') ∧
      c'.x * c'.y = R.nodeConst K' w ϖ' ^ (r * E) * (R.nodeConst K' w u₀ ^ E * uK') := by
  refine ⟨transport R w hKK' c, incl R w hKK' u, hu.map _, coe_incl R w hKK' u, ?_, ?_,
    ((hu₀.map _).pow E).mul (hu.map _), ?_⟩
  · rw [transport_x, coe_incl]
  · rw [transport_y, coe_incl]
  · have h := congrArg (incl R w hKK') hxy
    rw [map_mul, map_mul, map_pow, incl_nodeConst R w hKK' ϖ (ϖ' ^ r * u₀) hϖ, map_mul, map_pow] at h
    rw [transport_x, transport_y, h]
    ring

end DATUMTRANSPORT

end

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N))
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K')) (r : ℕ) (u₀ : ↥(NodeLocalized.coeffSubring A K')) (hu₀ : IsUnit u₀)
    (hϖ : (ϖ : AlgebraicClosure ℚ) = ((ϖ' ^ r * u₀ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ)) :
    ∃ (c' : R.NodeCoordinates K' w) (uK' : ↥(R.nodeIntegersOver K' w)), IsUnit uK' ∧
      ((uK' : ↥(modularFunctionFieldBar (N * q))) = u) ∧
      ((c'.x : ↥(modularFunctionFieldBar (N * q))) = c.x) ∧ ((c'.y : ↥(modularFunctionFieldBar (N * q))) = c.y) ∧
      IsUnit (R.nodeConst K' w u₀ ^ E * uK') ∧
      c'.x * c'.y = R.nodeConst K' w ϖ' ^ (r * E) * (R.nodeConst K' w u₀ ^ E * uK') :=
  DATUMTRANSPORT.main R w hKK' c ϖ E u hu hxy ϖ' r u₀ hu₀ hϖ

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le (solution)
